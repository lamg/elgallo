module Tests

open System
open Xunit
open FParsec
open RocqParser

let parseInductive text =
  match run (ws >>. inductiveType) text with
  | Success(r, _, _) -> r
  | Failure(msg, _, _) -> failwith msg

let typeParams names t =
  TypeParams.TypeParams(names, TypeExpr.Simple t)

let simpleParams name ts = TypeExpr.SimpleParams(name, ts)

[<Fact>]
let ``inductive day type`` () =
  let text =
    "    
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
  "

  let days =
    [ "monday"; "tuesday"; "wednesday"; "thursday"; "friday"; "saturday"; "sunday" ]
    |> List.map TypeExpr.Simple

  let expected =
    Inductive(newType = TypeExpr.Simple "day", baseType = TypeExpr.Simple "Type", cases = days)

  let actual = parseInductive text
  Assert.Equal<AST>(expected, actual)

[<Fact>]
let ``inductive color`` () =
  let text =
    "
Inductive color: Type :=
| bw (b: black_white)
| primary (p: rgb).
"

  let actual = parseInductive text

  let colors =
    [ simpleParams "bw" [ typeParams [ "b" ] "black_white" ]
      simpleParams "primary" [ typeParams [ "p" ] "rgb" ] ]

  let expected =
    Inductive(newType = TypeExpr.Simple "color", baseType = TypeExpr.Simple "Type", cases = colors)

  Assert.Equal<AST>(expected, actual)

[<Fact>]
let ``inductive with function`` () =
  let text =
    "
  Inductive bla : Type :=
  | gogo (f: nat -> nat).
"

  let actual = parseInductive text

  let expected =
    Inductive(
      newType = TypeExpr.Simple "bla",
      baseType = TypeExpr.Simple "Type",
      cases =
        [ simpleParams
            "gogo"
            [ TypeParams.TypeParams([ "f" ], TypeExpr.Func(TypeExpr.Simple "nat", TypeExpr.Simple "nat")) ] ]
    )

  Assert.Equal<AST>(expected, actual)
