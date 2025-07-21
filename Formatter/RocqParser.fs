module RocqParser

open FParsec

type TypeParams = TypeParams of names: list<string> * TypeExpr

and [<RequireQualifiedAccess>] TypeExpr =
  | Simple of string // O : nat
  | Func of TypeExpr * TypeExpr // nat -> nat
  | SimpleParams of string * TypeParams list // T (n m : nat) (j k: nat)

type AST =
  | Fixpoint
  | Inductive of newType: TypeExpr * baseType: TypeExpr * cases: TypeExpr list
  | Module

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
  many1Satisfy2L isIdStart isIdChar "identifier" .>> ws

let pint: Parser<int, unit> = pint32 .>> ws

let typeExpr =
  let expr, exprRef = createParserForwardedToRef ()

  let idsColon =
    parse {
      let! ids = many1 identifier
      do! token ":"
      let! e = expr
      return TypeParams(ids, e)
    }


  let typeParams = between (token "(") (token ")") idsColon

  exprRef.Value <-
    parse {
      let! id = identifier
      let! arrow = opt (kw "->")

      return!
        match arrow with
        | None ->
          parse {
            let! ts = many typeParams

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
    return Inductive(newType, baseType, cases)
  }
