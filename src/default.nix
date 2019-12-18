{ pkgs ? import <nixpkgs> {} }: with pkgs;

let
  prelude = builtins.fetchGit rec {
    name = "agda-prelude";
    url = "https://github.com/NixOS/nixpkgs.git";
    rev = "d193a94bfac9505148cb5cd1b68d08a08260b59c";
  };
in
stdenv.mkDerivation rec {
  name = "agdapkg";
  src = ./.;
  pname = name;
  tlType = "run";
  buildInputs = [ prelude haskellPackages.Agda texlive.combined.scheme-basic ];
}
