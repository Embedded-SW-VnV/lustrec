open Basetypes
open Corelang
open Datatype
(*open LustreSpec*)
open Lustre_types
open Str
module Y = Yojson.Basic

module type ParseExt =
sig
  val parse_condition : Y.t -> Condition.t
  val parse_action    : Y.t -> Action.t
  val parse_event     : Y.t -> Basetypes.event_t
end

module Parser (Ext : ParseExt) =
struct
  exception JSON_parse_error of string

  let path_split = String.split_on_char '/'
  let path_concat = String.concat (String.make 1 '/')

  module YU = Y.Util

  let to_list json =
    try
      json |> YU.to_list
    with
      YU.Type_error _ -> [ json ]

  let rec parse_prog json : prog_t =
    Logs.info  (fun m -> m "parse_prog %s" (json |> YU.member "name" |> YU.to_string));
      Program (
          json |> YU.member "name"        |> YU.to_string,
          (json |> YU.member "states"      |> to_list |> List.map parse_state) @
          (json |> YU.member "junctions"   |> to_list |> List.map parse_junction) @
            (json |> YU.member "sffunctions" |> to_list |> List.map
        (fun res  -> SFFunction (parse_prog res))),
        json |> YU.member "data"        |> to_list |> List.map parse_variable
        )

  and parse_state json =
    Logs.debug (fun m -> m "parse_state %s" (Y.to_string json));
    State (
        json |> YU.member "path" |> parse_path,
        json |> parse_state_def 
      )
  and parse_path json =
    Logs.debug (fun m -> m "parse_path %s" (json |> Y.to_string));
    json |> YU.to_string |> path_split
    
  and parse_state_def json =
    Logs.debug (fun m -> m "parse_state_def");
    {
      state_actions        = json |> YU.member "state_actions"        |> parse_state_actions;
      outer_trans          = json |> YU.member "outer_trans"          |> to_list |> List.map parse_transition;
      inner_trans          = json |> YU.member "inner_trans"          |> to_list |> List.map parse_transition;
      internal_composition = json |> YU.member "internal_composition" |> parse_internal_composition
      }

  and parse_state_actions json =
    Logs.debug (fun m -> m "parse_state_actions");
    {
      entry_act  = json |> YU.member "entry_act"  |> Ext.parse_action;
      during_act = json |> YU.member "during_act" |> Ext.parse_action;
      exit_act   = json |> YU.member "exit_act"   |> Ext.parse_action;
    }
  
  and parse_transition json =
    Logs.debug (fun m -> m "parse_transition %s" (Y.to_string json));
    {
      event          = json |> YU.member "event"          |> Ext.parse_event;
      condition      = json |> YU.member "condition" |> Ext.parse_condition;
      condition_act  =  json |> YU.member "condition_action"  |> Ext.parse_action;
      transition_act = json |> YU.member "transition_action" |> Ext.parse_action;
      dest           = json |> YU.member "dest"           |> parse_dest
      }
  and parse_dest json =
    Logs.debug (fun m -> m "parse_dest");
    let dest_type = json |> YU.member "type" |> YU.to_string in
    (dest_type |>
       (function
	| "State"    -> (fun p -> DPath p)
	| "Junction" -> (fun j -> DJunction (path_concat j))
	| _ -> raise (JSON_parse_error ("Invalid destination type: " ^ dest_type))))
      (json |> YU.member "name" |> parse_path)
  and parse_internal_composition json =
    Logs.debug (fun m -> m "parse_internal_composition");
    let state_type = json |> YU.member "type" |> YU.to_string in
    (state_type |>
       (function
	| "EXCLUSIVE_OR" -> (fun tinit substates ->                      Or  (tinit, substates))
	| "PARALLEL_AND" -> (fun tinit substates -> assert (tinit = []); And (substates))
        | _ -> raise (JSON_parse_error ("Invalid state type: " ^ state_type))))
      (json |> YU.member "tinit"  |> parse_tinit)
      (json |> YU.member "substates" |> to_list |> List.map YU.to_string)
    
  and parse_tinit json =
    Logs.debug (fun m -> m "parse_tinit %s" (Y.to_string json));
    json |> to_list |> List.map parse_transition 
    
  and parse_junction json =
    Logs.debug (fun m -> m "parse_junction");
    Junction (
        json |> YU.member "path"        |> YU.to_string,
        json |> YU.member "outer_trans" |> to_list |> List.map parse_transition
      )
  and scope_of_string s =
    match s with
    | "Constant"  -> Constant
    | "Input"     -> Input
    | "Local"     -> Local
    | "Output"    -> Output
    | "Parameter" -> Parameter
    | _           -> raise (JSON_parse_error ("Invalid scope for variable: " ^ s))
  and parse_real_value s =
    Logs.debug (fun m -> m "parse_real_value %s" s);
      let real_regexp_simp = regexp "\\(-?[0-9][0-9]*\\)\\.\\([0-9]*\\)" in
      let real_regexp_e    = regexp "\\(-?[0-9][0-9]*\\)\\.\\([0-9]*\\)\\(E\\|e\\)\\(\\(\\+\\|\\-\\)[0-9][0-9]*\\)" in
    if string_match real_regexp_e s 0 then
      let l = matched_group 1 s in
      let r = matched_group 2 s in
      let e = matched_group 4 s in
      Const_real (Real.create (l ^ r) 
                    (String.length r + (-1 * int_of_string e))
                    s)
    else
    if string_match real_regexp_simp s 0 then
      let l = matched_group 1 s in
      let r = matched_group 2 s in
      Const_real (Real.create (l ^ r)  (String.length r) s)
    else
      raise (JSON_parse_error ("Invalid real constant " ^ s))

  
and lustre_datatype_of_json json location =
    let datatype      = json |> YU.member "datatype"      |> YU.to_string in
    let initial_value = json |> YU.member "initial_value" |> YU.to_string in
    match datatype with
    | "bool" -> (Tydec_bool, mkexpr location
                   (Expr_const (Const_tag
                                  ((fun s -> match s with
                                     | "true"  -> tag_true
                                     | "false" -> tag_false
                                     | _       ->
                                       raise (JSON_parse_error ("Invalid constant for
     boolean: " ^ s))) initial_value))))
    | "int"  -> (Tydec_int, mkexpr location
                   (Expr_const (Const_int (int_of_string
                                             initial_value))))
    | "real" -> (Tydec_real, mkexpr location
                   (Expr_const (parse_real_value initial_value)))
    | _      -> raise (JSON_parse_error ("Invalid datatype " ^ datatype
                                         ^ " for variable " ^ (json |> YU.member "name"
                                                               |> YU.to_string)))
  and parse_variable json =
    Logs.debug (fun m -> m "parse_variable %s" (json |> YU.member "name" |> YU.to_string));
    let location                  = Location.dummy_loc in
    let (datatype, initial_value) = lustre_datatype_of_json json location in
    let vdecl = 
      mkvar_decl location ~orig:true
        ( json |> YU.member "name" |> YU.to_string,
          {ty_dec_desc = datatype;  ty_dec_loc = location},
          {ck_dec_desc = Ckdec_any; ck_dec_loc = location},
          true,
          Some initial_value,
          None (* no parentid *)
        )
    in
    { variable = vdecl; init_val = initial_value }
    
end

