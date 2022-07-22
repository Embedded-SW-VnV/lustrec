open Lustre_types
open Utils

(* This module is used to load lusic files when open(ing) modules in
   lustre/lusi sources *)

(* Load the provided program, either an actual program or a header lusi files:
   - reject program that define imported node
   - reject header that define lustre node
   - inject #include lus file into the program
   - loads #open lusic files
     - record the node name and check that they are uniquely defined
     - build the type/clock env from the imported nodes

   Returns an extended prog along with dependencies of #open and a type/clock base env. 
 *)
val load: is_header:bool -> program_t -> program_t * dep_t list * ( Typing.type_expr Env.t * Clocks.clock_expr Env.t)

(* Returns an updated env with the type/clock declaration of the program  *)
val get_envs_from_top_decls: program_t -> Typing.type_expr Env.t * Clocks.clock_expr Env.t
 
