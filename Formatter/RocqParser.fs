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

and Guard = Guard of Pattern * Expr

and [<RequireQualifiedAccess>] Pattern =
  | All
  | Identifier of string
  | Mixed of Pattern list
  | CommaSep of Pattern list

and [<RequireQualifiedAccess>] Expr =
  | Match of exprs: Expr list * guards: Guard list
  | Identifier of string
  | Apply of f: Expr * x: Expr
  | Binary of operator: Notation * left: Expr * right: Expr
  | IfThenElse of cond: Expr * thenExpr: Expr * elseExpr: Expr

[<RequireQualifiedAccess>]
type Level =
  | Plus
  | Minus
  | Asterisk


[<RequireQualifiedAccess>]
type Tactic =
  | Level of Level * depth: int * Tactic
  | Tactic of
    identifier: string *
    Direction option *
    destructedVar: string option *
    pattern: string list option *
    eqn: string option


[<RequireQualifiedAccess>]
type Proof =
  | TacticsQed of Tactic list
  | TacticsAdmitted of Tactic list
  | Tactics of Tactic list
  | Empty

type AST =
  | Definition of name: string * funcParams: TypeParams list * resultType: TypeExpr option * body: Expr
  | Fixpoint
  | Inductive of newType: TypeExpr * baseType: TypeExpr * cases: TypeExpr list
  | Module
  | RequireImport of longIdent: string list
  | Example of name: string * expression: Expr * proof: Proof
  | Notation of Notation

// tokenize

let comment = pstring "(*" >>. skipManyTill skipAnyChar (pstring "*)")
let ws = skipMany (spaces1 <|> comment)
let str s = pstring s .>> ws
let token s = pstring s >>. ws

let kw s =
  pstring s .>> notFollowedBy letter >>. ws

let identifier: Parser<string, unit> =
  let isIdStart c = isLetter c
  let isIdChar c = isLetter c || isDigit c || c = '_'
  let keywords = set [ "match"; "end"; "with" ]

  attempt (
    parse {
      let! i = many1Satisfy2L isIdStart isIdChar "identifier"
      let! apostrophes = many (pchar '\'') |>> System.String.Concat
      let id = i + apostrophes
      do! ws

      return!
        if keywords.Contains id then
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


let constructorPattern =
  let simple =
    identifier |>> Pattern.Identifier <|> (token "_" |>> fun _ -> Pattern.All)

  let mixed = many1 simple
  let commaSep = sepBy mixed (token ",")

  parse {
    let! xss = commaSep

    return
      match xss with
      | [ [ x ] ] -> x
      | [ xs ] -> Pattern.Mixed xs
      | _ -> xss |> List.map Pattern.Mixed |> Pattern.CommaSep
  }

let expression (operators: Map<string, Notation>) =
  let expr, exprRef = createParserForwardedToRef ()

  let factor =
    parse {
      let! xs = many1 (identifierExpr <|> betweenParens expr)

      return
        match xs with
        | [] -> failwith "factor should have parsed at least an element"
        | [ x ] -> x
        | y :: ys -> ys |> List.fold (fun acc y -> Expr.Apply(acc, y)) y
    }

  let guard =
    parse {
      let! pattern = constructorPattern
      do! token "=>"
      let! e = expr
      return Guard(pattern, e)
    }

  let matchExpr =
    parse {
      do! kw "match"
      let! exprs = sepBy1 expr (token ",")
      do! kw "with"
      let! guards = many1 (token "|" >>. guard)
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

  exprRef.Value <- matchExpr <|> term

  expr

let definition operators =
  parse {
    do! kw "Definition"
    let! name = identifier
    let! funcParams = many (typeParams typeExpr)
    let! resultType = opt (token ":" >>. typeExpr)
    do! token ":="
    let! e = expression operators
    do! token "."
    return Definition(name, funcParams, resultType, e)
  }

let kwStatement s = kw s .>> token "."

let innerTactic =
  // simpl.
  // rewrite <- a.
  //  destruct n as [| n' ] eqn:E.
  //  destruct b eqn:E.
  let pattern = kw "as" >>. between (str "[|") (str "]") (many1 identifier)
  let eqn = kw "eqn" >>. token ":" >>. identifier

  parse {
    let! id = identifier

    let! rewriteDirection =
      opt (
        token "<-" >>. preturn Direction.Right
        <|> (token "->" >>. preturn Direction.Left)
      )

    let! destructedVar = opt identifier
    let! pattern = opt pattern
    let! eqn = opt eqn
    do! token "."
    return Tactic.Tactic(id, rewriteDirection, destructedVar, pattern, eqn)
  }

let tactic =
  parse {
    let! level = many (str "-") <|> many (str "+") <|> many (str "*")
    let! innerTactic = innerTactic

    return!
      match level with
      | [] -> preturn innerTactic
      | "-" :: _ -> preturn (Tactic.Level(Level.Minus, level.Length, innerTactic))
      | "+" :: _ -> preturn (Tactic.Level(Level.Plus, level.Length, innerTactic))
      | "*" :: _ -> preturn (Tactic.Level(Level.Minus, level.Length, innerTactic))
      | _ -> fail $"unrecognized level pattern {level}"
  }

let splitLast xs =
  match List.rev xs with
  | [] -> failwith "splitLast does not accept empty lists"
  | y :: ys -> y, List.rev ys

let proof =
  parse {
    do! kwStatement "Proof"
    let! tactics = many tactic

    return
      match tactics with
      | [] -> Proof.Empty
      | _ ->
        match splitLast tactics with
        | Tactic.Tactic("Qed", _, _, _, _), xs -> Proof.TacticsQed xs
        | Tactic.Tactic("Admitted", _, _, _, _), xs -> Proof.TacticsAdmitted xs
        | _ -> Proof.Tactics tactics
  }

let example operators =
  parse {
    do! kw "Example"
    let! id = identifier
    do! token ":"
    let! e = expression operators
    do! token "."
    let! p = proof
    return Example(id, e, p)
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
//intros n.
//     destruct n as [| n' ] eqn:E.
//     destruct b eqn:E.
// intros [|n].
// intros [] [].

// Fixpoint
// Theorem
// Module

// | D, (A | B | C) => Lt
// m₁

// integers

// forall f: bool -> bool,
//     (forall x, f x = x) ->
//     forall b, f (f b) = b.
