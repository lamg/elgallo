module Tests

open System
open Xunit
open FParsec
open RocqParser


let parseWith parser text =
  match run (ws >>. parser) text with
  | Success(r, _, _) -> r
  | Failure(msg, _, _) -> failwith msg


let parseInductive text = parseWith inductiveType text

let parseRequireImport text = parseWith requireImport text

let typeParams names t =
  TypeParams.TypeParams(names, TypeExpr.Simple t)

let simpleParams name ts = TypeExpr.SimpleParams(name, ts)

let applyTwo f x y =
  Expr.Apply(Expr.Apply(Expr.Identifier f, Expr.Identifier x), Expr.Identifier y)

let applyOne f x =
  Expr.Apply(Expr.Identifier f, Expr.Identifier x)

let infixNotation op f x y =
  Notation.Basic(OperatorKind.Infix(op, x, y), applyTwo f x y)

let prefixNotation op f x =
  Notation.Basic(OperatorKind.Prefix(op, x), Expr.Apply(Expr.Identifier f, Expr.Identifier x))


let postfixNotation op f x =
  Notation.Basic(OperatorKind.Postfix(op, x), Expr.Apply(Expr.Identifier f, Expr.Identifier x))

let simpleTactic id = Tactic.Tactic(id, [])

let varTactic id vars =
  Tactic.Tactic(id, [ DestructedVars vars ])

let equal = infixNotation "=" "equal" "x" "y"
let implies = infixNotation "->" "implies" "x" "y"
let basicOperators = [ "=", equal; "->", implies ] |> Map.ofList

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
| primary (p: rgb)."

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
  | gogo (f: nat -> nat)."

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

[<Fact>]
let ``require import`` () =
  let text = "Require Import Coq.Init.Nat."
  let actual = parseRequireImport text
  let expected = RequireImport [ "Coq"; "Init"; "Nat" ]

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

  let actual = parseWith (definition Map.empty) text

  let expectedMatch =
    Expr.Match(
      [ Expr.Identifier "x" ],
      [ Guard(Pattern.Identifier "true", Expr.Identifier "true")
        Guard(Pattern.Identifier "false", Expr.Identifier "y") ]
    )

  let expected =
    Definition(
      "orb",
      [ typeParams [ "x" ] "bool"; typeParams [ "y" ] "bool" ],
      Some(TypeExpr.Simple "bool"),
      expectedMatch
    )

  Assert.Equal<AST>(expected, actual)


[<Fact>]
let ``comment parsing`` () =
  let text = "(* hello world *) Require Import Coq.Init.Nat."
  let actual = parseRequireImport text
  let expected = RequireImport [ "Coq"; "Init"; "Nat" ]

  Assert.Equal<AST>(expected, actual)


[<Fact>]
let ``binary expression`` () =
  let text = "a + b"
  let plus = infixNotation "+" "plus" "x" "y"
  let operators = [ "+", plus ] |> Map.ofSeq
  let actual = parseWith (expression operators) text
  let expected = Expr.Binary(plus, Expr.Identifier "a", Expr.Identifier "b")
  Assert.Equal<Expr>(expected, actual)

[<Fact>]
let ``function call`` () =
  let text = "f x"
  let actual = parseWith (expression Map.empty) text
  let expected = Expr.Apply(Expr.Identifier "f", Expr.Identifier "x")

  Assert.Equal<Expr>(expected, actual)

[<Fact>]
let ``match f x`` () =
  let text =
    "
match f x with
| Coq y => false
| Rocq z => true
end
  "

  let actual = parseWith (expression Map.empty) text

  let expected =
    Expr.Match(
      [ Expr.Apply(Expr.Identifier "f", Expr.Identifier "x") ],
      [ Guard(
          Pattern.Mixed[Pattern.Identifier "Coq"
                        Pattern.Identifier "y"],
          Expr.Identifier "false"
        )
        Guard(
          Pattern.Mixed[Pattern.Identifier "Rocq"
                        Pattern.Identifier "z"],
          Expr.Identifier "true"
        ) ]
    )

  Assert.Equal<Expr>(expected, actual)

[<Fact>]
let ``various patterns`` () =
  [ "Coq x y", Pattern.Mixed [ Pattern.Identifier "Coq"; Pattern.Identifier "x"; Pattern.Identifier "y" ]
    "Coq _ _",
    Pattern.Mixed[Pattern.Identifier "Coq"
                  Pattern.All
                  Pattern.All]
    "Coq _, Rocq _",
    Pattern.CommaSep
      [ Pattern.Mixed[Pattern.Identifier "Coq"
                      Pattern.All]
        Pattern.Mixed[Pattern.Identifier "Rocq"
                      Pattern.All] ] ]
  |> List.iter (fun (text, expected) ->
    let actual = parseWith constructorPattern text
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
      "test_next_working_day",
      LawKind.Example,
      Demonstrandum(
        [],
        Expr.Binary(
          equal,
          Expr.Apply(Expr.Identifier "next_working_day", applyOne "next_working_day" "saturday"),
          Expr.Identifier "tuesday"
        )
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
    Assert.Equal<Notation>(expected, actual))

[<Fact>]
let tactics () =
  [ "destruct n as [|n'] eqn:E.", Tactic.Tactic("destruct", [ DestructedVars [ "n" ]; Patterns [ [ "n'" ] ]; Eqn "E" ])
    "destruct b eqn:E.", Tactic.Tactic("destruct", [ DestructedVars [ "b" ]; Eqn "E" ])
    "induction n as [|n' ind].", Tactic.Tactic("induction", [ DestructedVars["n"]; Patterns [ [ "n'"; "ind" ] ] ])
    "rewrite <- a.", Tactic.Tactic("rewrite", [ Direction Direction.Right; DestructedVars [ "a" ] ])
    "intros n m.", Tactic.Tactic("intros", [ DestructedVars [ "n"; "m" ] ])
    "intros [] [].", Tactic.Tactic("intros", [ EmptyBrackets; EmptyBrackets ]) ]
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
      Expr.Binary(equal, Expr.Identifier "x", Expr.Identifier "y")
    )

  let forallVars = [ [ "x"; "y" ], None ]
  let demonstrandum = Demonstrandum(forallVars, demExpr)

  let intro_a_tree =
    Tree(
      Tactic.Level(Level.Minus 1, simpleTactic "simpl"),
      [ Tree(
          Tactic.Level(Level.Plus 1, varTactic "intro" [ "a" ]),
          [ Tree(varTactic "rewrite" [ "a" ], []); Tree(simpleTactic "reflexivity", []) ]
        ) ]
    )

  let proof =
    [ Tree(Tactic.Tactic("intros", [ DestructedVars [ "x"; "y" ] ]), [])
      Tree(Tactic.Tactic("destruct", [ DestructedVars["x"]; Eqn "E" ]), [ intro_a_tree; intro_a_tree ]) ]
    |> Proof.Qed


  let expected = Law("andb_eq_orb", LawKind.Theorem, demonstrandum, proof)

  match expected, actual with
  | AST.Law(_, _, d, p), AST.Law(_, _, e, q) ->
    Assert.Equal<Proof>(p, q)
    Assert.Equal<Demonstrandum>(d, e)
    Assert.Equal<AST>(expected, actual)
  | _ -> failwith "expecting a law"
