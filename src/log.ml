(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

let report ?plugin:(modulename="") ?(verbose_level=Options.verbose_level) ~level:level p =
if !verbose_level >= level then
  begin
    if modulename="" then
      Format.eprintf "%t" p
    else
      Format.eprintf "[%s] @[%t@]" modulename p
  end

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)

