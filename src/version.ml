let number = "@PACKAGE_VERSION@-@GITBRANCH@"

let codename = "@VERSION_CODENAME@"

let include_path = Sites.Sites.include_ |> List.hd

let testgen_path = Sites.Sites.testgen |> List.hd
