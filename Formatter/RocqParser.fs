module RocqParser

open FParsec

type TypeParams = TypeParams of names: list<string> * TypeExpr

and [<RequireQualifiedAccess>] TypeExpr =
  | Simple of string // O : nat
  | Func of TypeExpr * TypeExpr // nat -> nat
  | SimpleParams of string * TypeParams list // T (n m : nat) (j k: nat)

type Operator = Operator of symbol: string * precedence: int

type Guard = Guard of Pattern * Expr

and [<RequireQualifiedAccess>] Pattern =
  | All
  | Identifier of string

and [<RequireQualifiedAccess>] Expr =
  | Match of exprs: Expr list * guards: Guard list
  | Identifier of string
  | Apply of f: Expr * x: Expr
  | Binary of operator: Operator * left: Expr * right: Expr
  | IfThenElse of cond: Expr * thenExpr: Expr * elseExpr: Expr

type AST =
  | Definition of name: string * funcParams: TypeParams list * resultType: TypeExpr option * body: Expr
  | Fixpoint
  | Inductive of newType: TypeExpr * baseType: TypeExpr * cases: TypeExpr list
  | Module
  | RequireImport of longIdent: string list

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
      do! ws

      return!
        if keywords.Contains i then
          fail $"keyword {i} not a valid identifier"
        else
          preturn i
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

let expression (operators: Map<string, Operator>) =
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
      let! pattern = token "_" >>. preturn Pattern.All <|> (identifier |>> Pattern.Identifier)
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
