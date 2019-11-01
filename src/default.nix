{ pkgs ? import <nixos-19> {} }: with pkgs;

stdenv.mkDerivation rec {
  name = "agdapkg";
  src = ./.;
  pname = name;
  tlType = "run";
  buildInputs = [ haskellPackages.Agda texlive.combined.scheme-basic ];
}
