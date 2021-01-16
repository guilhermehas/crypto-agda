{ pkgs ? import <nixpkgs> {}
, nixos-18 ? import <nixos-18> {}
}: with pkgs;

let
  agdapkg = nixos-18.callPackage src/default.nix {};
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
