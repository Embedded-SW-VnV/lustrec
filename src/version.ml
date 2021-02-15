let number = "%%VERSION%%"

let codename () =
  match "%%VERSION_NUM%%" with
  | "1.7" -> "Xia/Huai-dev"
  | _ -> "dev"

let include_path = Sites.Sites.include_ |> List.hd
let testgen_path = Sites.Sites.testgen |> List.hd
