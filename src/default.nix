{ pkgs ? import <nixpkgs> {} }: with pkgs;

stdenv.mkDerivation rec {
  name = "agdapkg";
  src = ./.;
  pname = name;
  tlType = "run";
  buildInputs = [ haskellPackages.Agda agdaPrelude texlive.combined.scheme-basic ];
  configurePhase = ''
     export PRELUDE=${agdaPrelude}
  '';
}
