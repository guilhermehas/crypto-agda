{ pkgs ? import <nixos-19> {} }: with pkgs;

let
  agdapkg = (import src/default.nix) {};
in
stdenv.mkDerivation {
  name = "master-thesis";
  src = ./.;
  buildInputs = [
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
