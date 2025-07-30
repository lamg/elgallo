module FileTree

open System

type FileTree = Dir of files: string seq * FileTree seq

let fileTreeWithExtension (extension: string) =
  let rec loop (dir: string) =
    let files =
      dir |> IO.Directory.GetFiles |> Seq.filter (fun f -> f.EndsWith extension)

    let directories =
      dir
      |> IO.Directory.GetDirectories
      |> Seq.filter (fun f -> f.StartsWith "." |> not)
      |> Seq.map loop

    Dir(files, directories)


  IO.Directory.GetCurrentDirectory() |> loop

let rec iterTree (f: string -> unit) (tree: FileTree) =
  let (Dir(files, subdirs)) = tree
  files |> Seq.iter f
  subdirs |> Seq.iter (iterTree f)
