module Program

open System
open FileTree

let formatRocq () =
  let tree = fileTreeWithExtension ".v"

  let formatFile (file: string) =
    match Parsers.Rocq.parse file with
    | Ok p ->
      let newContent = Formatter.format p |> List.toArray
      IO.File.WriteAllLines(file, newContent)
    | Error e -> eprintfn $"{e}"

  iterTree formatFile tree

[<EntryPoint>]
let main _ =
  formatRocq ()
  0
