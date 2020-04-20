{ pkgs ? import <nixpkgs> {} }: with pkgs;

let
  agdapkg = callPackage src/default.nix {};
in
stdenv.mkDerivation {
  name = "master-thesis";
  src = ./.;
  buildInputs = [
    which
    (texlive.combine {
        inherit (texlive)
          scheme-full
        ;
        simple-package = {
          pkgs = [ agdapkg ];
        };
      })
  ];
}
