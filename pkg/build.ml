#!/usr/bin/env ocaml
#directory "pkg"
#use "topkg.ml"

let ocamlbuild =
  "ocamlbuild -use-ocamlfind -classic-display -plugin-tag"

let () =
  let oc = open_out "tests/_tags" in
  output_string oc (if Env.native then "<*.ml>: ppx_native" else "<*.ml>: ppx_byte");
  close_out oc

let () =
  Pkg.describe "ppx_hardcaml" ~builder:`OCamlbuild [
    Pkg.lib "pkg/META";
    Pkg.bin ~auto:true "src/ppx_hardcaml" ~dst:"../lib/ppx_hardcaml/ppx_hardcaml";
    Pkg.doc "README.org";
    Pkg.doc "LICENSE"]
