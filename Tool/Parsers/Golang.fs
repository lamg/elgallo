module Parsers.Golang

open FParsec

type AST =
  | Function
  | Type
  | Import
  | Package of name: string * AST list
