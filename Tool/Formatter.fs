module Formatter

open Parsers.Rocq

let indent (spaces: int) (lines: string list) =
  let leading = String.init spaces (fun _ -> " ")
  leading :: lines

let arrangeExceedingWidth (width: int) (topLevel: AST, lines: string list) = lines

let format (file: AST) : string list =
  match file with
  | AST.Check(e, t) -> []
  | AST.Compute e -> []
  | AST.Function f -> []
  | AST.Inductive(newType, baseType, cases) -> []
  | AST.Law(id, kind, expr, proof) -> []
  | AST.Module(id, toplevels) -> []
  | AST.Notation n -> []
  | AST.RequireImport r -> []
