module Parsers.Util

open System
open System.Globalization
open FParsec

type Identifier =
  | ShortId of string
  | LongId of string * Identifier

  member this.Head =
    match this with
    | ShortId n -> n
    | LongId(n, _) -> n

type Tokenizer =
  | WithCommentBlock of startToken: string * endToken: string * keywords: string list
  | WithCommentLine of startCommentLine: string * Tokenizer

  member this.startEndCommentBlock =
    match this with
    | WithCommentBlock(startToken, endToken, _) -> startToken, endToken
    | WithCommentLine(_, t) -> t.startEndCommentBlock

  member this.langKeywords =
    match this with
    | WithCommentBlock(_, _, keywords) -> Set keywords
    | WithCommentLine(_, t) -> t.langKeywords

  member this.commentBlock =
    let startToken, endToken = this.startEndCommentBlock
    pstring startToken >>. skipManyTill skipAnyChar (pstring endToken)

  member this.commentLine =
    match this with
    | WithCommentLine(startComment, _) -> pstring startComment >>. skipManyTill skipAnyChar newline
    | _ -> preturn ()

  member this.ws = skipMany (spaces1 <|> this.commentBlock)

  member this.str s = pstring s .>> this.ws

  member this.kw s =
    pstring s .>> notFollowedBy letter >>. this.ws

  member this.identifier: Parser<Identifier, unit> =
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

    let shortId =
      parse {
        let! i = many1Satisfy2L isIdStart isIdChar "identifier"
        let! apostrophes = many (pchar '\'') |>> System.String.Concat
        let id = i + apostrophes

        return!
          if this.langKeywords.Contains id || id = "_" then
            fail $"keyword {id} not a valid identifier"
          else
            preturn id
      }

    let longId = sepBy1 shortId (attempt (pchar '.' >>? lookAhead shortId))

    parse {
      let! id = longId
      do! this.ws

      return
        match List.rev id with
        | [] -> failwith "should have returned at least a short identifier"
        | x :: xs -> xs |> List.fold (fun acc x -> Identifier.LongId(x, acc)) (ShortId x)
    }
    |> attempt

  member this.pint: Parser<int, unit> = pint32 .>> this.ws
  member this.token s = pstring s >>. this.ws

  member this.betweenParens p =
    between (this.token "(") (this.token ")") p
