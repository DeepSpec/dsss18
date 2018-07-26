#!/usr/bin/env ocaml
#use "topfind";;
#require "topkg"
open Topkg

let () =
  Pkg.describe "verdi-runtime" @@ fun c ->
    Ok [ Pkg.lib "src/Util.cmi";
	 Pkg.lib "src/Opts.cmi";
	 Pkg.lib "src/Daemon.cmi";
	 Pkg.lib "src/Shim.cmi";
	 Pkg.lib "src/DisklessShim.cmi";
	 Pkg.lib "src/OrderedShim.cmi";
	 Pkg.lib "src/UnorderedShim.cmi";
	 Pkg.lib "src/DynamicShim.cmi";
	 Pkg.lib "src/DiskOpShim.cmi";
	 Pkg.lib "src/verdi_runtime.a";
	 Pkg.lib "src/verdi_runtime.cma";
	 Pkg.lib "src/verdi_runtime.cmxa";
	 Pkg.lib "src/verdi_runtime.cmxs" ]
