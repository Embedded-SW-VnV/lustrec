open Yojson.Safe

val prune_str: string -> t -> t
val prune_null_assoc: t -> t
val to_list_content_str: string -> t -> t
val flatten_ivd: t -> t
val flatten_numeric_literal: t -> t
val to_list_str: string -> t -> t
