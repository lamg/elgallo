module Parsers.Rocq

open FParsec

type TypeParams = TypeParams of names: Util.Identifier list * TypeExpr

and [<RequireQualifiedAccess>] TypeExpr =
  | Simple of Util.Identifier // O : nat
  | Func of TypeExpr * TypeExpr // nat -> nat
  | SimpleParams of Util.Identifier * TypeParams list // T (n m : nat) (j k: nat)

[<RequireQualifiedAccess>]
type OperatorKind =
  | Infix of op: string * left: Util.Identifier * right: Util.Identifier // x + y
  | Prefix of op: string * right: Util.Identifier // !x
  | Postfix of op: string * left: Util.Identifier // x!
  | Mixfix of OperatorKind list // Notation "'if' c 'then' t 'else' e" := (if c then t else e).

  member this.OperatorString =
    match this with
    | Postfix(op, _)
    | Prefix(op, _)
    | Infix(op, _, _) -> op
    | Mixfix xs -> xs |> List.map _.OperatorString |> String.concat "_"

[<RequireQualifiedAccess>]
type Direction =
  | Left
  | Right

[<RequireQualifiedAccess>]
type Notation =
  | Basic of OperatorKind * Expr
  | AtLevel of Notation * atLevel: int
  | Associative of Notation * Direction

  member this.NotationString =
    match this with
    | Basic(k, _) -> k.OperatorString
    | AtLevel(n, _)
    | Associative(n, _) -> n.NotationString

and [<RequireQualifiedAccess>] Guard =
  | Guard of Pattern * Expr
  | Pattern of Pattern

and [<RequireQualifiedAccess>] Pattern =
  | All
  | Identifier of Util.Identifier
  | ConstructorWithParams of Pattern list
  | CommaSep of Pattern list
  | NestedAlt of Pattern list

and [<RequireQualifiedAccess>] Expr =
  | Match of exprs: Expr list * guards: Guard list
  | Identifier of Util.Identifier
  | Integer of int
  | Apply of f: Expr * x: Expr
  | Binary of operator: Notation * left: Expr * right: Expr
  | IfThenElse of cond: Expr * thenExpr: Expr * elseExpr: Expr
  | Forall of (Util.Identifier list * TypeExpr option) list * expr: Expr

[<RequireQualifiedAccess>]
type Level =
  | Plus of int
  | Minus of int
  | Asterisk of int
  | Base

type TacticArgument =
  | Direction of Direction
  | DestructedVars of Util.Identifier list
  | Patterns of Util.Identifier list list
  | Eqn of Util.Identifier
  | EmptyBrackets

[<RequireQualifiedAccess>]
type Tactic =
  | Level of Level * Tactic
  | Tactic of identifier: Util.Identifier * args: TacticArgument list

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
  { name: Util.Identifier
    functionParams: TypeParams list
    resultType: TypeExpr option
    body: Expr
    functionType: FunctionType }

type AST =
  | Function of Function
  | Inductive of newType: TypeExpr * baseType: TypeExpr * cases: TypeExpr list
  | Module of identifier: Util.Identifier * toplevels: AST list
  | RequireImport of Util.Identifier
  | Law of name: Util.Identifier * kind: LawKind * Expr * proof: Proof
  | Notation of Notation
  | Check of Expr * TypeExpr
  | Compute of Expr

// tokenize

let tokenizer =
  Util.WithCommentBlock("(*", "*)", [ "match"; "end"; "with"; "as"; "eqn"; "End"; "Definition" ])

let comment: Parser<unit, unit> = tokenizer.commentBlock

let identifier: Parser<Util.Identifier, unit> = tokenizer.identifier
let token = tokenizer.token
let betweenParens = tokenizer.betweenParens
let kw = tokenizer.kw
let ws = tokenizer.ws
let str = tokenizer.str
let pint = tokenizer.pint

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
    let! id = identifier
    do! token "."
    return RequireImport id
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
  //  destruct n as [| n' ] eqn:E. TODO allow [x | y | z]
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
  let qed, admitted =
    Util.Identifier.ShortId "Qed", Util.Identifier.ShortId "Admitted"

  let proofEnd =
    str $"{qed.Head}." |>> (fun _ -> Tactic.Tactic(qed, []))
    <|> (str $"{admitted.Head}." |>> fun _ -> Tactic.Tactic(admitted, []))

  let rec tactics () =
    parse {
      let! t = proofEnd <|> tactic

      return!
        match t with
        | Tactic.Tactic(n, _) when n = qed || n = admitted -> preturn [ t ]
        | _ ->
          parse {
            let! ts = tactics ()
            return t :: ts
          }
    }

  parse {
    do! kwStatement "Proof"
    let! tactics = tactics ()

    return
      match tactics with
      | [] -> Proof.Incomplete []
      | _ ->
        match splitLast tactics with
        | Tactic.Tactic(n, _), tacticsButLast when n = qed -> tacticsButLast |> tacticsAsTree |> Proof.Qed
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

    return Notation r
  }
  <?> "notation"

let check operators =
  parse {
    do! kw "Check"
    let! e = expression operators
    do! token ":"
    let! te = typeExpr
    do! token "."
    return AST.Check(e, te)
  }

let rec topLevelDefinitions (moduleId: Util.Identifier option) operators =
  let moduleEnd =
    match moduleId with
    | Some mid ->
      parse {
        do! kw "End"
        let! _ = str mid.Head
        do! token "."
        return None
      }
    | None -> eof |>> fun _ -> None

  parse {
    let def =
      law operators
      <|> notation operators
      <|> rocqFunction operators
      <|> inductiveType
      <|> rocqModule operators
      <|> check operators
      |>> Some

    let! defOrEnd = def <|> moduleEnd

    return!
      match defOrEnd with
      | Some(Notation n as d) ->
        parse {
          let! rs = topLevelDefinitions moduleId (Map.add n.NotationString n operators)
          return d :: rs
        }
      | Some d ->
        parse {
          let! rs = topLevelDefinitions moduleId operators
          return d :: rs
        }
      | None -> preturn []
  }

and rocqModule operators =
  parse {
    do! kw "Module"
    let! id = identifier
    do! token "."
    let! topLevels = topLevelDefinitions (Some id) operators
    return Module(id, topLevels)
  }
