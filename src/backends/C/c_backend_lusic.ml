open Lusic
open Utils.Format

let print_lusic_to_h basename extension =
  let module HeaderMod = C_backend_header.EmptyMod in
  let module Header = C_backend_header.Main (HeaderMod) in
  let lusic = read_lusic basename extension in
  let header_name = basename ^ ".h" in
  with_out_file header_name @@ fun h_fmt ->
  assert (not lusic.obsolete);
  (*Format.eprintf "lusic to h: %i items.@." (List.length lusic.contents);*)
  (* Typing.uneval_prog_generics lusic.contents;
     * Clock_calculus.uneval_prog_generics lusic.contents; *)
  Header.print_header_from_header
    h_fmt
    (Filename.basename basename)
    lusic.contents
