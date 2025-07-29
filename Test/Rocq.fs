module Tests

open System
open Xunit
open FParsec
open Parsers.Rocq
open Parsers.Util

let parseWith parser text =
  match run (ws >>. parser) text with
  | Success(r, _, _) -> r
  | Failure(msg, _, _) -> failwith msg

let tryParseWith parser text =
  match run parser text with
  | Success(r, _, _) -> Some r
  | _ -> None

let parseInductive text = parseWith inductiveType text

let parseRequireImport text = parseWith requireImport text

let typeParams names t =
  TypeParams.TypeParams(names, TypeExpr.Simple t)

let simpleParams name ts = TypeExpr.SimpleParams(ShortId name, ts)

let applyTwo f x y =
  Expr.Apply(Expr.Apply(Expr.Identifier(ShortId f), Expr.Identifier(ShortId x)), Expr.Identifier(ShortId y))

let applyOne f x =
  Expr.Apply(Expr.Identifier(ShortId f), Expr.Identifier(ShortId x))

let infixNotation op f x y =
  Notation.Basic(OperatorKind.Infix(op, ShortId x, ShortId y), applyTwo f x y)

let prefixNotation op f x =
  Notation.Basic(OperatorKind.Prefix(op, ShortId x), Expr.Apply(Expr.Identifier(ShortId f), Expr.Identifier(ShortId x)))


let postfixNotation op f x =
  Notation.Basic(
    OperatorKind.Postfix(op, ShortId x),
    Expr.Apply(Expr.Identifier(ShortId f), Expr.Identifier(ShortId x))
  )

let simpleTactic id = Tactic.Tactic(ShortId id, [])

let varTactic id vars =
  Tactic.Tactic(ShortId id, [ DestructedVars vars ])

let equal = infixNotation "=" "equal" "x" "y"
let implies = infixNotation "->" "implies" "x" "y"
let basicOperators = [ "=", equal; "->", implies ] |> Map.ofList

let x = ShortId "x"
let y = ShortId "y"
let z = ShortId "z"
let f = ShortId "f"
let a = ShortId "a"
let b = ShortId "b"
let trueId = ShortId "true"
let falseId = ShortId "false"
let boolId = ShortId "bool"

let requireImportNat = RequireImport(LongId("Coq", LongId("Init", ShortId "Nat")))

[<Fact>]
let identifiers () =
  [ "id", Some "id"; "_", None; "m₀", Some "m₀"; "ℓ", Some "ℓ"; "ℓ_", Some "ℓ_" ]
  |> List.iter (fun (text, expected) ->
    let actual = tryParseWith identifier text
    Assert.Equal(Option.map ShortId expected, actual))

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
    |> List.map (ShortId >> TypeExpr.Simple)

  let expected =
    Inductive(newType = TypeExpr.Simple(ShortId "day"), baseType = TypeExpr.Simple(ShortId "Type"), cases = days)

  let actual = parseInductive text
  Assert.Equal<AST>(expected, actual)

[<Fact>]
let ``inductive color`` () =
  let text =
    "
Inductive color: Type :=
| bw (b: black_white)
| primary (p: rgb)."

  let actual = parseInductive text

  let colors =
    [ simpleParams "bw" [ typeParams [ ShortId "b" ] (ShortId "black_white") ]
      simpleParams "primary" [ typeParams [ ShortId "p" ] (ShortId "rgb") ] ]

  let expected =
    Inductive(newType = TypeExpr.Simple(ShortId "color"), baseType = TypeExpr.Simple(ShortId "Type"), cases = colors)

  Assert.Equal<AST>(expected, actual)

[<Fact>]
let ``inductive with function`` () =
  let text =
    "
  Inductive bla : Type :=
  | gogo (f: nat -> nat)."

  let actual = parseInductive text

  let expected =
    Inductive(
      newType = TypeExpr.Simple(ShortId "bla"),
      baseType = TypeExpr.Simple(ShortId "Type"),
      cases =
        [ simpleParams
            "gogo"
            [ TypeParams.TypeParams(
                [ ShortId "f" ],
                TypeExpr.Func(TypeExpr.Simple(ShortId "nat"), TypeExpr.Simple(ShortId "nat"))
              ) ] ]
    )

  Assert.Equal<AST>(expected, actual)

[<Fact>]
let ``require import`` () =
  let text = "Require Import Coq.Init.Nat."
  let actual = parseRequireImport text
  let expected = requireImportNat

  Assert.Equal<AST>(expected, actual)

[<Fact>]
let ``definition orb`` () =
  let text =
    "
Definition orb (x: bool) (y: bool): bool :=
  match x with
  | true => true
  | false => y
  end.
  "

  let actual = parseWith (rocqFunction Map.empty) text

  let expectedMatch =
    Expr.Match(
      [ Expr.Identifier x ],
      [ Guard.Guard(Pattern.Identifier trueId, Expr.Identifier trueId)
        Guard.Guard(Pattern.Identifier falseId, Expr.Identifier y) ]
    )

  let expected =
    Function
      { name = ShortId "orb"
        functionParams = [ typeParams [ x ] boolId; typeParams [ y ] boolId ]
        resultType = Some(TypeExpr.Simple boolId)
        body = expectedMatch
        functionType = Definition }

  Assert.Equal<AST>(expected, actual)


[<Fact>]
let ``comment parsing`` () =
  let text = "(* hello world *) Require Import Coq.Init.Nat."
  let actual = parseRequireImport text

  Assert.Equal<AST>(requireImportNat, actual)


[<Fact>]
let ``simple expressions`` () =
  let plus = infixNotation "+" "plus" "x" "y"
  let operators = [ "+", plus ] |> Map.ofSeq

  [ "x+y", Expr.Binary(plus, Expr.Identifier x, Expr.Identifier y)
    "11", Expr.Integer 11 ]
  |> List.iter (fun (text, expected) ->
    let actual = parseWith (expression operators) text
    Assert.Equal<Expr>(expected, actual))

[<Fact>]
let ``function call`` () =
  let text = "f x"
  let actual = parseWith (expression Map.empty) text
  let expected = Expr.Apply(Expr.Identifier f, Expr.Identifier x)

  Assert.Equal<Expr>(expected, actual)

[<Fact>]
let ``forall expression`` () =
  let text =
    "
    forall f: bool -> bool,
    (forall x, f x = x) ->
    forall b, f (f b) = b"

  let boolT = TypeExpr.Simple boolId

  let left =
    Expr.Forall([ [ x ], None ], Expr.Binary(equal, applyOne "f" "x", Expr.Identifier x))

  let ffb = Expr.Apply(Expr.Identifier f, applyOne "f" "b")

  let right = Expr.Forall([ [ b ], None ], Expr.Binary(equal, ffb, Expr.Identifier b))

  let body = Expr.Binary(implies, left, right)
  let expected = Expr.Forall([ [ f ], Some(TypeExpr.Func(boolT, boolT)) ], body)
  let actual = parseWith (expression basicOperators) text
  Assert.Equal<Expr>(expected, actual)


[<Fact>]
let ``match f x`` () =
  let text =
    "
match f x with
| Coq y => false
| Rocq z => true
| (A | B) => false
end
  "

  let actual = parseWith (expression Map.empty) text

  let expected =
    Expr.Match(
      [ Expr.Apply(Expr.Identifier f, Expr.Identifier x) ],
      [ Guard.Guard(
          Pattern.ConstructorWithParams[Pattern.Identifier(ShortId "Coq")
                                        Pattern.Identifier y],
          Expr.Identifier falseId
        )
        Guard.Guard(
          Pattern.ConstructorWithParams[Pattern.Identifier(ShortId "Rocq")
                                        Pattern.Identifier z],
          Expr.Identifier trueId
        )
        Guard.Guard(
          Pattern.NestedAlt [ Pattern.Identifier(ShortId "A"); Pattern.Identifier(ShortId "B") ],
          Expr.Identifier falseId
        ) ]
    )

  Assert.Equal<Expr>(expected, actual)

[<Fact>]
let ``various patterns`` () =
  let coq = ShortId "Coq"
  let rocq = ShortId "Rocq"
  let A = ShortId "A"
  let B = ShortId "B"
  let C = ShortId "C"

  [ "Coq x y", Pattern.ConstructorWithParams [ Pattern.Identifier coq; Pattern.Identifier x; Pattern.Identifier y ]
    "Coq _ _",
    Pattern.ConstructorWithParams[Pattern.Identifier coq
                                  Pattern.All
                                  Pattern.All]
    "Coq _, Rocq _",
    Pattern.CommaSep
      [ Pattern.ConstructorWithParams[Pattern.Identifier coq
                                      Pattern.All]
        Pattern.ConstructorWithParams[Pattern.Identifier rocq
                                      Pattern.All] ]
    "A, (B | C)",
    Pattern.CommaSep
      [ Pattern.Identifier A
        Pattern.NestedAlt [ Pattern.Identifier B; Pattern.Identifier C ] ] ]
  |> List.iter (fun (text, expected) ->
    let actual = parseWith pattern text
    Assert.Equal<Pattern>(expected, actual))

[<Fact>]
let ``example parsing`` () =
  let text =
    "
Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. simpl. reflexivity. Qed."

  let actual = parseWith (law basicOperators) text

  let expected =
    Law(
      ShortId "test_next_working_day",
      LawKind.Example,
      Expr.Binary(
        equal,
        Expr.Apply(Expr.Identifier(ShortId "next_working_day"), applyOne "next_working_day" "saturday"),
        Expr.Identifier(ShortId "tuesday")
      ),
      Proof.Qed [ Tree(simpleTactic "simpl", []); Tree(simpleTactic "reflexivity", []) ]

    )

  Assert.Equal<AST>(expected, actual)

[<Fact>]
let notation () =
  [ """Notation "x && y" := (andb x y).""", infixNotation "&&" "andb" "x" "y"
    """Notation "!y" := (not y).""", prefixNotation "!" "not" "y"
    """Notation "x!" := (not x).""", postfixNotation "!" "not" "x"
    """Notation "x + y" := (add x y) (at level 50, left associativity).""",
    Notation.Associative(Notation.AtLevel(infixNotation "+" "add" "x" "y", 50), Direction.Left) ]
  |> List.iter (fun (text, expected) ->
    let actual = parseWith (notation Map.empty) text

    Assert.Equal<AST>(Notation expected, actual))

[<Fact>]
let tactics () =
  [ "destruct n as [|n'] eqn:E.",
    Tactic.Tactic(
      ShortId "destruct",
      [ DestructedVars [ ShortId "n" ]
        Patterns [ [ ShortId "n'" ] ]
        Eqn(ShortId "E") ]
    )
    "destruct b eqn:E.", Tactic.Tactic(ShortId "destruct", [ DestructedVars [ ShortId "b" ]; Eqn(ShortId "E") ])
    "induction n as [|n' ind].",
    Tactic.Tactic(
      ShortId "induction",
      [ DestructedVars[ShortId "n"]
        TacticArgument.Patterns [ [ ShortId "n'"; ShortId "ind" ] ] ]
    )
    "rewrite <- a.", Tactic.Tactic(ShortId "rewrite", [ Direction Direction.Right; DestructedVars [ ShortId "a" ] ])
    "intros n m.", Tactic.Tactic(ShortId "intros", [ DestructedVars [ ShortId "n"; ShortId "m" ] ])
    "intros [] [].", Tactic.Tactic(ShortId "intros", [ EmptyBrackets; EmptyBrackets ]) ]
  |> List.iter (fun (text, expected) ->
    let actual = parseWith innerTactic text
    Assert.Equal<Tactic>(expected, actual))

[<Fact>]
let ``theorem with forall`` () =
  let text =
    "
Theorem andb_eq_orb:
    forall x y,
    (andb x y = orb x y) ->
    x = y.
  Proof.
    intros x y.
    destruct x eqn:E.
    - simpl.
      + intro a. rewrite a. reflexivity.
    - simpl.
      + intro a. rewrite a. reflexivity.
  Qed."

  let actual = parseWith (law basicOperators) text

  let demExpr =
    Expr.Binary(
      implies,
      Expr.Binary(equal, applyTwo "andb" "x" "y", applyTwo "orb" "x" "y"),
      Expr.Binary(equal, Expr.Identifier x, Expr.Identifier y)
    )

  let forallVars = [ [ x; y ], None ]
  let demonstrandum = Expr.Forall(forallVars, demExpr)

  let intro_a_tree =
    Tree(
      Tactic.Level(Level.Minus 1, simpleTactic "simpl"),
      [ Tree(
          Tactic.Level(Level.Plus 1, varTactic "intro" [ a ]),
          [ Tree(varTactic "rewrite" [ a ], []); Tree(simpleTactic "reflexivity", []) ]
        ) ]
    )

  let proof =
    [ Tree(Tactic.Tactic(ShortId "intros", [ DestructedVars [ x; y ] ]), [])
      Tree(Tactic.Tactic(ShortId "destruct", [ DestructedVars[x]; Eqn(ShortId "E") ]), [ intro_a_tree; intro_a_tree ]) ]
    |> Proof.Qed


  let expected = Law(ShortId "andb_eq_orb", LawKind.Theorem, demonstrandum, proof)

  match expected, actual with
  | AST.Law(_, _, d, p), AST.Law(_, _, e, q) ->
    Assert.Equal<Proof>(p, q)
    Assert.Equal<Expr>(d, e)
    Assert.Equal<AST>(expected, actual)
  | _ -> failwith "expecting a law"


[<Fact>]
let ``parse toplevels`` () =
  let text =
    """
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition orb (x: bool) (y: bool): bool :=
  match x with
  | true => true
  | false => y
  end.

Example not_true_and_false:
  (andb (negb true) false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).

Notation "x || y" := (orb x y).

Example or_notation:
  true || false = true.
Proof.  reflexivity. Qed.

Example and_notation:
  true && false = false.
Proof. reflexivity. Qed.

Definition invert (x: black_white): black_white :=
  if x then white else black.

Check (negb true):bool.

Check negb: bool -> bool.

Module Playground.
  Definition foo: rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo: rgb.
Check foo:bool.
  """

  let actual = parseWith (topLevelDefinitions None basicOperators) text
  printfn "$actual {actual}"
