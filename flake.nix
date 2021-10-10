{
  description = "JSstar";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-20.09";
    fstar-flake.url = "github:W95Psp/nix-flake-fstar";
  };
  
  outputs = { self, nixpkgs, flake-utils, fstar-flake }:
    flake-utils.lib.eachSystem [ "x86_64-darwin" "x86_64-linux"]
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          master = fstar-flake.defaultPackage.${system};
          tools = fstar-flake.lib.x86_64-linux.fstar;
          fstar = tools.perform-fstar-to-ocaml master
            (
              master.overrideAttrs 
                (o: {patches = [
                       ./patches/restore-unicode.patch
                       ./patches/reflect-ranges.diff
                     ];
                    })
            );
          lib = pkgs.lib;
        in  
          rec {
            packages = {
              fstar = fstar;
            };
            devShell = pkgs.mkShell {
              name = "dev-env-jsstar";
              buildInputs = fstar.buildInputs ++ [
                fstar
                (let 
                  ocaml_packages = ["fstarlib" "fstar-tactics-lib" "fstar-compiler-lib"];
                in
                  pkgs.writeScriptBin "build"
                    ''addEnvHooks(){ :; }
                      source ${pkgs.ocamlPackages.findlib.setupHook}
                      addOCamlPath ${fstar}
                      fstar.exe --odir out --codegen OCaml --extract 'JS +JS.* +Doc' JS.fst
                      cd out
                      ocamlbuild -use-ocamlfind -cflag -g -package ${builtins.concatStringsSep "," ocaml_packages} JS.cmxa
                  ''
                )
              ];
            };
          }
      );
}



 # ocamlbuild -use-ocamlfind -cflag -g -package ${builtins.concatStringsSep "," ocaml_packages} ${translate-fst-module module}.cmxa
