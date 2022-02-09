open Format
open Unix

module S = struct
  include Set.Make(String)
  let pp fmt = iter (fprintf fmt "%s@;")
end

module ST = struct
  include Set.Make(
    struct
      type t = string * int * int * float
      let compare (x1, _, _, _) (x2, _, _, _) = compare x1 x2
    end)
  let pp fmt = iter (fun (x, loc, n, t) -> fprintf fmt "%s %d %d %f@;" x loc n t)
end

module STF = struct
  include Set.Make(
    struct
      type t = string * (int * int) option
      let compare (x1, _) (x2, _) = compare x1 x2
    end)
  let pp fmt = iter (fun (x, o) -> fprintf fmt "%s %a@;" x
                        (pp_print_option (fun fmt (r, g) -> fprintf fmt "%d %d" r g)) o)
end

module M = Map.Make(Int)

type report = {
  compiled: S.t;
  verified: ST.t M.t;
  failed: STF.t;
  ninits: S.t
}
let empty_report = {
  compiled = S.empty;
  verified = M.empty;
  failed = STF.empty;
  ninits = S.empty
}

let dir = "../../../offline_tests_build"

let _ = try Unix.mkdir dir 0o755 with _ -> ()

let report_f = Filename.concat dir "report"

let section h = "# " ^ h

let end_section = "##"

let compiled_section = section "COMPILED"

let ninit_section = section "BAD_INIT"

let initial_timeout = 15

let next_timeout r =
  2 * M.fold (fun i _ n -> max i n) r.verified initial_timeout

let timeout_section i = section (sprintf "TIMEOUT %d" i)

let timeout_of_section h =
  match Re.Str.(split (regexp_string " ")) h with
  | ["#"; "TIMEOUT"; i] -> Some (int_of_string i)
  | _ -> None

let failed_section = section "FAILED"

let is_compiled report f =
  S.mem f report.compiled

let add_compiled report f =
  { report with compiled = S.add f report.compiled }

let is_ninit report f =
  S.mem f report.ninits

let add_ninit report f =
  { report with ninits = S.add f report.ninits }

let is_verified report f =
  M.exists (fun _ -> ST.exists (fun (x, _, _, _) -> x = f)) report.verified

let add_verified report i f loc n t =
  { report with verified = M.update i (fun s ->
        let s = match s with None -> ST.empty | Some s -> s in
        Some (ST.add (f, loc, n, t) s)) report.verified }

let is_failed report f =
  STF.exists (fun (x, _) -> x = f) report.failed

let add_failed report ?goals f =
  { report with failed = STF.add (f, goals) report.failed }

let parse_report () =
  try
    let ic = open_in report_f in
    let rec read_compiled r =
      try match input_line ic with
        | "" -> read_compiled r
        | f -> if f = end_section then r else read_compiled (add_compiled r f)
      with End_of_file -> r
    in
    let rec read_verified i r =
      try match input_line ic with
        | "" -> read_verified i r
        | f ->
          if f = end_section then r
          else match String.split_on_char ' ' f with
            | [f; loc; n; t] ->
              read_verified i
                (add_verified r i f
                   (int_of_string loc) (int_of_string n) (float_of_string t))
            | _ -> assert false
      with End_of_file -> r
    in
    let rec read_ninits r =
      try match input_line ic with
        | "" -> read_ninits r
        | f -> if f = end_section then r else read_ninits (add_ninit r f)
      with End_of_file -> r
    in
    let rec read_failed r =
      try match input_line ic with
        | "" -> read_failed r
        | f -> if f = end_section then r
          else match String.split_on_char ' ' f with
            | [f; res; goa] ->
              read_failed (add_failed r ~goals:(int_of_string res, int_of_string goa) f)
            | f :: _ ->
              read_failed (add_failed r f)
            | _ -> assert false
      with End_of_file -> r
    in
    let rec read r =
      try match input_line ic with
        | "" ->
          read r
        | f when f = compiled_section ->
          read (read_compiled r)
        | f when f = failed_section ->
          read (read_failed r)
        | f when f = ninit_section ->
          read (read_ninits r)
        | f ->
          let r = match timeout_of_section f with
            | Some i -> read_verified i r
            | None -> r
          in
          read r
      with End_of_file -> r
    in
    let r = read empty_report in
    close_in ic;
    r
  with _ -> empty_report

let pp_compiled fmt report =
  fprintf fmt "%s@;%a%s@;"
    compiled_section
    S.pp report.compiled
    end_section

let pp_failed fmt report =
  fprintf fmt "%s@;%a%s@;"
    failed_section
    STF.pp report.failed
    end_section

let pp_ninits fmt report =
  fprintf fmt "%s@;%a%s@;"
    ninit_section
    S.pp report.ninits
    end_section

let pp_verified fmt report =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "%s@;" end_section)
    (fun fmt (i, s) -> fprintf fmt "%s@;%a" (timeout_section i) ST.pp s)
    fmt
    (List.sort (fun (i, _) (j, _) -> compare i j) (M.bindings report.verified))

let pp_report fmt report =
  fprintf fmt "@[<v>%a@;%a@;%a@;%a@]@."
    pp_compiled report
    pp_ninits report
    pp_failed report
    pp_verified report

let write_report report =
  let oc = open_out report_f in
  let fmt = formatter_of_out_channel oc in
  pp_report fmt report;
  close_out oc

let config_format_tags =
  set_tags true;
  let mark_open_stag = function
    | String_tag "bold" -> "\x1b[1m"
    | String_tag "red" -> "\x1b[31m"
    | String_tag "magenta" -> "\x1b[35m"
    | String_tag "green" -> "\x1b[32m"
    | _ -> ""
  in
  let mark_close_stag _ = "\x1b[0m" in
  let stag_fns = get_formatter_stag_functions () in
  set_formatter_stag_functions { stag_fns with mark_open_stag; mark_close_stag }

let pp_header fmt =
  fprintf fmt "@{<bold>%s:@}"

let max_l = ref 0

let err_f = "/tmp/err"

let read_whole_file f =
  let ch = open_in f in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let has_warning log =
  let open Re.Str in
  let reg = "Warning: Generating stateful spec for uninitialized state variable" in
  try
    search_forward (regexp reg) log 0 |> ignore;
    true
  with Not_found -> false

let print_result p f fmt_str check =
  printf "%3.0f%% %-*s %(%s%)@." p !max_l f fmt_str check

let print_results ok ko w n =
  printf "OK: @{<green>%d@} (@{<red>%d@} + @{<magenta>%d@}) / %d@." ok ko w n

let compile report lustrec fs =
  printf "@.%a@." pp_header "Compilation tests";
  max_l := List.fold_left (fun m f -> let n = String.length f in max n m) 0 fs;
  let n = List.length fs in
  let n_f = float_of_int n in
  let report, ok, ko, ninits, _ =
    List.fold_left (fun (report, ok, ko, ninits, i) f ->
        let i' = i + 1 in
        let p = float_of_int i' *. 100. /. n_f in
        let success r : _ * _ * _ * _ * _ format * _ =
          r, ok + 1, ko, ninits, "@{<green>%s@}", "OK"
        in
        let ninit r : _ * _ * _ * _ * _ format * _ =
          r, ok, ko, ninits + 1, "@{<magenta>%s@}", "NI"
        in
        let fail r log : _ * _ * _ * _ * _ format * _ =
          r, ok, ko + 1, ninits, "@{<red>%s@}", "KO\n" ^ log
        in
        let report, ok, ko, ninits, fmt_str, check =
          if is_compiled report f then success report
          else if is_ninit report f then ninit report
          else
            let cmd = Filename.quote_command ~stderr:err_f lustrec
                ["-acsl-spec"; "-d"; dir; f]
            in
            let ic = open_process_in cmd in
            let b = match close_process_in ic with
              | WEXITED r -> r = 0
              | _ -> false
            in
            let log = read_whole_file err_f in
            if b then
              if has_warning log
              then ninit (add_ninit report f)
              else success (add_compiled report f)
            else
              fail report log
        in
        print_result p f fmt_str check;
        write_report report;
        report, ok, ko, ninits, i')
      (report, 0, 0, 0, 0) fs
  in
  print_results ok ko ninits n;
  report

let frama_c = "frama-c"
let wp_provers =
  [
    "alt-ergo";
    "z3";
    "cvc4"
  ] |> String.concat ","
let wp_models =
  [
    "ref";
    "real"
  ] |> String.concat ","
let wp_timeout = 60 |> string_of_int
let wp_par = 48 |> string_of_int
let wp_cache = "none"
(* let wp_cache_dir = Filename.concat dir "cache" *)
let wp_args =
  [
    "-wp";
    "-wp-prover";    wp_provers;
    "-wp-model";     wp_models;
    "-wp-no-warn-memory-model";
    "-wp-timeout";   wp_timeout;
    "-wp-par";       wp_par;
    (* "-wp-cache-dir"; wp_cache_dir *)
    "-wp-cache";     wp_cache;
  ]
let wp_module = "strategy.ml"
let wp_strategy = "LustreC"
let wp_auto_depth = 100 |> string_of_int
let wp_strategy_args =
  [
    "-wp";
    "-wp-prover";     wp_provers;
    "-load-module";   wp_module;
    "-wp-auto";       wp_strategy;
    "-wp-auto-depth"; wp_auto_depth;
  ]
let frama_c_args f =
  wp_args
  @ f
    :: "-then"
    :: wp_strategy_args
let frama_c_cmd f = frama_c :: frama_c_args f

let goals log =
  let open Re.Str in
  let reg = "\\([0-9]+\\) / \\([0-9]+\\)" in
  let rec aux acc i =
    try
      let j = search_forward (regexp reg) log i in
      let i = j + String.length (matched_string log) in
      let resolved = matched_group 1 log |> int_of_string in
      let goals = matched_group 2 log |> int_of_string in
      let acc = match acc with
        | Some (r, _) -> Some (r + resolved, r + goals)
        | None -> Some (resolved, goals)
      in
      aux acc i
    with Not_found -> acc
  in
  aux None 0

let get_loc f =
  let open Yojson.Safe in
  let open Util in
  let cmd = Filename.quote_command ~stdout:err_f "tokei" ["-o"; "json"; f] in
  let ic = open_process_in cmd in
  match close_process_in ic with
  | WEXITED 0 ->
    begin try
        from_file err_f |> member "C" |> member "code" |> to_int
      with _ -> -1
    end
  | _ -> -1

let rec verify report timeout fs =
  if fs <> [] then begin
    printf "@.%a@."
      pp_header (sprintf "Verification tests - %is timeout" timeout);
    let n = List.length fs in
    let n_f = float_of_int n in
    let report, ok, ko, tm, _, fs =
      List.fold_left (fun (report, ok, ko, tm, i, fs) f ->
          let f' = Filename.remove_extension f ^ ".c" in
          let f'' = Filename.concat dir f' in
          let i' = i + 1 in
          let p = float_of_int i' *. 100. /. n_f in
          let success ?(already=false) r : _ * _ * _ * _ * _ format * _ * _ =
            r, ok + 1, ko, tm, "@{<green>%s@}",
            ("OK" ^ if already then " (A)" else ""), fs
          in
          let fail ?(already=false) r : _ * _ * _ * _ * _ format * _ * _ =
            r, ok, ko + 1, tm, "@{<red>%s@}",
            ("KO" ^ if already then " (A)" else "\n" ^ read_whole_file err_f), fs
          in
          let tm r f : _ * _ * _ * _ * _ format * _ * _ =
            r, ok, ko, tm + 1, "@{<magenta>%s@}", "TO", f :: fs
          in
          let report, ok, ko, tm, fmt_str, check, fs =
            if is_verified report f' then success ~already:true report
            else if is_failed report f' then fail ~already:true report
            else
              let cmd = Filename.quote_command ~stdout:err_f "timeout"
                  (string_of_int timeout :: frama_c_cmd f'')
              in
              let t = Unix.gettimeofday () in
              let ic = open_process_in cmd in
              match close_process_in ic with
              | WEXITED 0 ->
                let t = Unix.gettimeofday () -. t in
                let log = read_whole_file err_f in
                begin match goals log with
                  | Some (n, m) ->
                    if n = m then
                      success (add_verified report timeout f' (get_loc f'') n t)
                    else
                      fail (add_failed report ~goals:(n, m) f')
                  | None -> fail (add_failed report f')
                end
              | WEXITED 124 ->
                tm report f
              | _ ->
                fail (add_failed report f')
          in
          print_result p f' fmt_str check;
          write_report report;
          report, ok, ko, tm, i', fs)
        (report, 0, 0, 0, 0, []) fs
    in
    print_results ok ko tm n;
    verify report (timeout * 2) fs
  end

let print_ignored fs =
  printf "@.@[<v 2>%a@;%a@]@."
    pp_header "Ignored tests"
    (pp_print_list pp_print_string) fs

let () =
  let lustrec = Sys.argv.(1) in
  let lus_fs = Sys.argv.(2) |> Re.Str.(split (regexp_string " ")) in
  let ignored_f = Sys.argv.(3) in
  let ignored_fs =
    let ic = open_in ignored_f in
    let rec read fs =
      try
        read (input_line ic :: fs)
      with End_of_file -> fs
    in
    let fs = read [] in
    close_in ic;
    fs
  in
  let report = parse_report () in
  let report = compile report lustrec lus_fs in
  let ignored_fs = ignored_fs
                   @ List.map Filename.chop_extension (S.elements report.ninits)
  in
  print_ignored (List.map (fun f -> f ^ ".c") ignored_fs);
  let lus_fs =
    List.(sort_uniq compare
            (filter (fun f ->
                 not (mem (Filename.chop_extension f) ignored_fs)) lus_fs))
  in
  verify report (next_timeout report) lus_fs
