module Parsers.Util

open System
open System.Globalization
open FParsec

type Tokenizer =
  | WithCommentBlock of startToken: string * endToken: string * keywords: string list

  member this.commentBlock =
    let (WithCommentBlock(startToken, endToken, _)) = this
    pstring startToken >>. skipManyTill skipAnyChar (pstring endToken)

  member this.ws = skipMany (spaces1 <|> this.commentBlock)

  member this.str s = pstring s .>> this.ws

  member this.kw s =
    pstring s .>> notFollowedBy letter >>. this.ws

  member this.identifier: Parser<string, unit> =
    let (WithCommentBlock(_, _, keywords)) = this
    let keywords = Set keywords
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

    attempt (
      parse {
        let! i = many1Satisfy2L isIdStart isIdChar "identifier"
        let! apostrophes = many (pchar '\'') |>> System.String.Concat
        let id = i + apostrophes
        do! this.ws

        return!
          if keywords.Contains id || id = "_" then
            fail $"keyword {id} not a valid identifier"
          else
            preturn id
      }
    )

  member this.pint: Parser<int, unit> = pint32 .>> this.ws
  member this.token s = pstring s >>. this.ws

  member this.betweenParens p =
    between (this.token "(") (this.token ")") p
