module RocqParser

open FParsec

type TypeParams = TypeParams of names: list<string> * TypeExpr

and [<RequireQualifiedAccess>] TypeExpr =
  | Simple of string // O : nat
  | Func of TypeExpr * TypeExpr // nat -> nat
  | SimpleParams of string * TypeParams list // T (n m : nat) (j k: nat)

[<RequireQualifiedAccess>]
type OperatorKind =
  | Infix of op: string * left: string * right: string // x + y
  | Prefix of op: string * right: string // !x
  | Postfix of op: string * left: string // x!
  | Mixfix of OperatorKind list // Notation "'if' c 'then' t 'else' e" := (if c then t else e).

[<RequireQualifiedAccess>]
type Direction =
  | Left
  | Right

[<RequireQualifiedAccess>]
type Notation =
  | Basic of OperatorKind * Expr
  | AtLevel of Notation * atLevel: int
  | Associative of Notation * Direction

and [<RequireQualifiedAccess>] Guard =
  | Guard of Pattern * Expr
  | Pattern of Pattern

and [<RequireQualifiedAccess>] Pattern =
  | All
  | Identifier of string
  | ConstructorWithParams of Pattern list
  | CommaSep of Pattern list
  | NestedAlt of Pattern list

and [<RequireQualifiedAccess>] Expr =
  | Match of exprs: Expr list * guards: Guard list
  | Identifier of string
  | Integer of int
  | Apply of f: Expr * x: Expr
  | Binary of operator: Notation * left: Expr * right: Expr
  | IfThenElse of cond: Expr * thenExpr: Expr * elseExpr: Expr
  | Forall of (string list * TypeExpr option) list * expr: Expr

[<RequireQualifiedAccess>]
type Level =
  | Plus of int
  | Minus of int
  | Asterisk of int
  | Base

type TacticArgument =
  | Direction of Direction
  | DestructedVars of string list
  | Patterns of string list list
  | Eqn of string
  | EmptyBrackets

[<RequireQualifiedAccess>]
type Tactic =
  | Level of Level * Tactic
  | Tactic of identifier: string * args: TacticArgument list

  member this.TacticLevel =
    match this with
    | Level(l, _) -> l
    | _ -> Level.Base

  member this.Identifier =
    match this with
    | Level(_, t) -> t.Identifier
    | Tactic(id, _) -> id

type Tree<'a> =
  | Tree of value: 'a * children: Tree<'a> list

  member this.Value =
    let (Tree(v, _)) = this
    v

  member this.Children =
    let (Tree(_, xs)) = this
    xs

[<RequireQualifiedAccess>]
type Proof =
  | Qed of Tree<Tactic> list
  | Incomplete of Tree<Tactic> list

type LawKind =
  | Lemma
  | Theorem
  | Example

type FunctionType =
  | Definition
  | Fixpoint

type Function =
  { name: string
    functionParams: TypeParams list
    resultType: TypeExpr option
    body: Expr
    functionType: FunctionType }

type AST =
  | Function of Function
  | Inductive of newType: TypeExpr * baseType: TypeExpr * cases: TypeExpr list
  | Module
  | RequireImport of longIdent: string list
  | Law of name: string * kind: LawKind * Expr * proof: Proof
  | Notation of Notation

// tokenize

let comment = pstring "(*" >>. skipManyTill skipAnyChar (pstring "*)")
let ws = skipMany (spaces1 <|> comment)
let str s = pstring s .>> ws
let token s = pstring s >>. ws

let kw s =
  pstring s .>> notFollowedBy letter >>. ws

open System
open System.Globalization

let identifier: Parser<string, unit> =

  let isIdStart c = Char.IsLetter c || c = '_'

  let isIdChar (c: char) =
    match CharUnicodeInfo.GetUnicodeCategory c with
    | UnicodeCategory.UppercaseLetter
    | UnicodeCategory.LowercaseLetter
    | UnicodeCategory.TitlecaseLetter
    | UnicodeCategory.ModifierLetter
    | UnicodeCategory.OtherLetter
    | UnicodeCategory.OtherNumber
    | UnicodeCategory.DecimalDigitNumber
    | UnicodeCategory.NonSpacingMark
    | UnicodeCategory.SpacingCombiningMark -> true
    | _ -> c = '_'

  let keywords = set [ "match"; "end"; "with"; "as"; "eqn" ]

  attempt (
    parse {
      let! i = many1Satisfy2L isIdStart isIdChar "identifier"
      let! apostrophes = many (pchar '\'') |>> System.String.Concat
      let id = i + apostrophes
      do! ws

      return!
        if keywords.Contains id || id = "_" then
          fail $"keyword {id} not a valid identifier"
        else
          preturn id
    }
  )

let pint: Parser<int, unit> = pint32 .>> ws

let betweenParens p = between (token "(") (token ")") p

let typeParams expr =
  let idsColon =
    parse {
      let! ids = many1 identifier
      do! token ":"
      let! e = expr
      return TypeParams(ids, e)
    }

  betweenParens idsColon

let typeExpr =
  let expr, exprRef = createParserForwardedToRef ()

  exprRef.Value <-
    parse {
      let! id = identifier
      let! arrow = opt (kw "->")

      return!
        match arrow with
        | None ->
          parse {
            let! ts = many (typeParams expr)

            return
              match ts with
              | [] -> TypeExpr.Simple id
              | _ -> TypeExpr.SimpleParams(id, ts)
          }
        | Some _ ->
          parse {
            let! rest = exprRef.Value
            return TypeExpr.Func(TypeExpr.Simple id, rest)
          }
    }

  expr

let inductiveType =
  parse {
    do! kw "Inductive"
    let! newType = typeExpr
    do! token ":"
    let! baseType = typeExpr
    do! token ":="
    let! cases = many1 (token "|" >>. typeExpr)
    do! token "."
    return Inductive(newType, baseType, cases)
  }

let requireImport =
  parse {
    do! kw "Require"
    do! kw "Import"
    let! xs = sepEndBy1 identifier (pstring ".")
    do! ws
    return RequireImport xs
  }

let identifierExpr = identifier |>> Expr.Identifier

let pattern =
  let constructorPattern nested =
    let simple =
      identifier |>> Pattern.Identifier
      <|> (token "_" |>> fun _ -> Pattern.All)
      <|> nested

    let mixed =
      parse {
        let! xs = many1 simple

        return
          match xs with
          | [ x ] -> x
          | _ -> Pattern.ConstructorWithParams xs
      }

    parse {
      let! xs = sepBy mixed (token ",")

      return
        match xs with
        | [ x ] -> x
        | _ -> Pattern.CommaSep xs
    }


  let nestedAlternatives inner =
    parse {
      let! nested = betweenParens (sepBy inner (token "|"))
      return Pattern.NestedAlt nested
    }

  let pat, patRef = createParserForwardedToRef ()
  let nested = nestedAlternatives pat
  let basic = constructorPattern nested
  patRef.Value <- basic
  pat

let expression (operators: Map<string, Notation>) =
  let expr, exprRef = createParserForwardedToRef ()
  let integer = pint |>> Expr.Integer

  let factor =
    parse {
      let! xs = many1 (identifierExpr <|> integer <|> betweenParens expr)

      return
        match xs with
        | [] -> failwith "factor should have parsed at least an element"
        | [ x ] -> x
        | y :: ys -> ys |> List.fold (fun acc y -> Expr.Apply(acc, y)) y
    }

  let guard =
    let fullGuard pattern =
      parse {
        do! token "=>"
        let! e = expr
        return Guard.Guard(pattern, e)
      }

    parse {
      do! token "|"
      let! p = pattern
      return! fullGuard p <|> preturn (Guard.Pattern p)
    }

  let matchExpr =
    parse {
      do! kw "match"
      let! exprs = sepBy1 expr (token ",")
      do! kw "with"
      let! guards = many1 guard
      do! kw "end"
      return Expr.Match(exprs, guards)
    }

  let binaryTail left =
    parse {
      let! op = operators |> Map.toSeq |> Seq.map (fst >> str) |> choice
      let! right = expr
      return Expr.Binary(operators[op], left, right)
    }

  let term =
    parse {
      let! t = factor
      let! r = binaryTail t <|> preturn t
      return r
    }

  let forall =
    let varDecl =
      parse {
        let! vars = many1 identifier
        let! typeSpec = opt (token ":" >>. typeExpr)
        return vars, typeSpec
      }

    let simpleDecl = varDecl |>> List.singleton
    let varDecls = simpleDecl <|> many1 (betweenParens varDecl)

    parse {
      do! kw "forall"
      let! decls = varDecls
      do! token ","
      let! e = expr
      return Expr.Forall(decls, e)
    }

  exprRef.Value <- matchExpr <|> forall <|> term

  expr

let rocqFunction operators =
  parse {
    let! functionType = kw "Definition" >>. preturn Definition <|> (kw "Fixpoint" >>. preturn Fixpoint)
    let! name = identifier
    let! funcParams = many (typeParams typeExpr)
    let! resultType = opt (token ":" >>. typeExpr)
    do! token ":="
    let! e = expression operators
    do! token "."

    return
      Function
        { name = name
          functionParams = funcParams
          resultType = resultType
          body = e
          functionType = functionType }
  }

let kwStatement s = kw s .>> token "."

let innerTactic =
  // simpl.
  // rewrite <- a.
  //  destruct n as [| n' ] eqn:E.
  //  destruct b eqn:E.
  let pattern = kw "as" >>. between (str "[|") (str "]") (many1 identifier)
  let eqn = kw "eqn" >>. token ":" >>. identifier |>> Eqn
  let emptyBrackets = token "[" >>. token "]" >>. preturn EmptyBrackets

  let rewriteDirection =
    token "<-" >>. preturn Direction.Right
    <|> (token "->" >>. preturn Direction.Left)
    |>> Direction

  let destructedVar = many1 identifier |>> DestructedVars

  let pat = pattern |>> fun x -> Patterns [ x ]

  parse {
    let! id = identifier
    let! args = many (rewriteDirection <|> destructedVar <|> pat <|> eqn <|> emptyBrackets)
    do! token "."
    return Tactic.Tactic(id, args)
  }


let tactic =
  parse {
    let! level = many (str "-" <|> str "+" <|> str "*")
    let! innerTactic = innerTactic

    return!
      match level with
      | [] -> preturn innerTactic
      | "-" :: _ -> preturn (Tactic.Level(Level.Minus level.Length, innerTactic))
      | "+" :: _ -> preturn (Tactic.Level(Level.Plus level.Length, innerTactic))
      | "*" :: _ -> preturn (Tactic.Level(Level.Minus level.Length, innerTactic))
      | _ -> fail $"unrecognized level pattern {level}"
  }

let splitLast xs =
  match List.rev xs with
  | [] -> failwith "splitLast does not accept empty lists"
  | y :: ys -> y, List.rev ys

/// given a list of tactics creates a list of tactic trees according the
/// proper nesting level of each tactic
let rec tacticsAsTree (tactics: Tactic list) =
  let initial =
    tactics
    |> List.takeWhile (fun t -> t.TacticLevel = Level.Base)
    |> List.map (fun x -> Tree(x, []))

  let remaining = tactics |> List.skip initial.Length

  match remaining with
  | [] -> initial
  | y :: ys ->

    let segments, rm =
      y :: ys
      |> List.fold
        (fun (acc, currentSegment) y' ->
          if y'.TacticLevel = y.TacticLevel then
            List.rev currentSegment :: acc, [ y' ]
          else
            acc, y' :: currentSegment)
        ([], [])

    let segments = segments @ [ List.rev rm ]

    let treeSegments =
      segments
      |> List.filter (_.IsEmpty >> not)
      |> List.map (function
        | [] -> failwith "internal error: segment must be non-empty"
        | y :: ys -> Tree(y, tacticsAsTree ys))


    match initial with
    | [] -> treeSegments
    | _ ->
      let last, init = splitLast initial
      init @ [ Tree(last.Value, treeSegments) ]

let proof =
  parse {
    do! kwStatement "Proof"
    let! tactics = many tactic

    return
      match tactics with
      | [] -> Proof.Incomplete []
      | _ ->
        match splitLast tactics with
        | Tactic.Tactic("Qed", _), tacticsButLast -> tacticsButLast |> tacticsAsTree |> Proof.Qed
        | _, _ -> tacticsAsTree tactics |> Proof.Incomplete
  }

let kwValue k v = kw k >>. preturn v

let law operators =
  parse {
    let! kind =
      choice
        [ kwValue "Example" LawKind.Example
          kwValue "Theorem" LawKind.Theorem
          kwValue "Lemma" LawKind.Lemma ]

    let! id = identifier
    do! token ":"
    let! body = expression operators
    do! token "."
    let! proof = proof
    return Law(id, kind, body, proof)
  }

let doubleQuoted = between (str "\"") (str "\"")

let rocqString =
  let str s = pstring s
  let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> '"')

  let escapedChar =
    str "\\"
    >>. (anyOf "\\\"nrt"
         |>> function
           | 'n' -> "\n"
           | 'r' -> "\r"
           | 't' -> "\t"
           | c -> string c)

  between (str "\"") (str "\"") (stringsSepBy normalCharSnippet escapedChar)
  .>> ws

let rocqOperatorString =
  let isOperatorChar c =
    match c with
    | '!'
    | '#'
    | '$'
    | '%'
    | '&'
    | '*'
    | '+'
    | '-'
    | '.'
    | '/'
    | ':'
    | '<'
    | '='
    | '>'
    | '?'
    | '@'
    | '^'
    | '|'
    | '~'
    | '\\'
    | '`' -> true
    | _ -> false

  let operator = many1Satisfy isOperatorChar .>> ws <?> "operator"

  let prefix =
    parse {
      let! op = operator
      let! right = identifier
      return OperatorKind.Prefix(op, right)
    }

  let postfixOrInfix =
    parse {
      let! left = identifier
      let! op = operator
      let! right = opt identifier

      return
        match right with
        | None -> OperatorKind.Postfix(op, left)
        | Some right -> OperatorKind.Infix(op, left, right)
    }

  doubleQuoted (prefix <|> postfixOrInfix) <?> "notation string"

let notation operators =
  // Notation "x + y" := (Nat.add x y) (at level 50, left associativity).
  let atLevel notation =
    parse {
      do! kw "at"
      do! kw "level"
      let! level = pint
      return Notation.AtLevel(notation, level)
    }
    <|> preturn notation
    <?> "at level specifier"

  let assocDir notation =
    parse {
      do! token ","

      let! dir =
        kw "left" >>. preturn Direction.Left
        <|> (kw "right" >>. preturn Direction.Right)

      do! kw "associativity"
      return Notation.Associative(notation, dir)
    }
    <|> preturn notation
    <?> "associativity specifier"

  let notationOptional notation =
    betweenParens (
      parse {
        let! level = atLevel notation
        let! assoc = assocDir level
        return assoc
      }
    )
    <|> preturn notation
    <?> "notation optional"

  parse {
    do! kw "Notation"
    let! op = rocqOperatorString
    do! token ":="
    let! e = betweenParens (expression operators)
    let! r = notationOptional (Notation.Basic(op, e))
    do! token "."
    return r
  }
  <?> "notation"



// TODO

// Module

// integers
