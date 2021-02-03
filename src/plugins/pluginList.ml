let registered : (module PluginType.S) list ref = ref []

let plugins () = !registered
