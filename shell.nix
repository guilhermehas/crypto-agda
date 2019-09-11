let
  # Look here for information about how to generate `nixpkgs-version.json`.
  #  → https://nixos.wiki/wiki/FAQ/Pinning_Nixpkgs
  pinnedVersion = builtins.fromJSON (builtins.readFile ./.nixpkgs-version.json);
  pinnedPkgs = import (builtins.fetchGit {
    inherit (pinnedVersion) url rev;

    ref = "nixos-unstable";
  }) {};
  agdapkg = (import src/default.nix) {};
in

# This allows overriding pkgs by passing `--arg pkgs ...`
{ pkgs ? pinnedPkgs }:

with pkgs;

mkShell {
  buildInputs = [
    # put packages here.
    (texlive.combine {
        inherit (texlive)
        xcolor
        geometry
        hyperref
        fontspec
        textpos
        isodate
        titlesec
        latexmk
        blindtext
        substr

        url
        amsmath
        parskip
        fancyhdr
        vmargin

        apacite
        logreq
        biblatex
        changepage

        polytable
        lazylist
        environ
        trimspaces
        ucs
        catchfilebetweentags

        xifthen
        ifnextok
        currfile
        noindentafter
        ifmtarg
        scheme-medium
        listings
        minted
        microtype
        babel
        todonotes
        chngcntr
        ifplatform
        xstring
        minifp
        titlecaps
        enumitem
        l3packages
        ;
        simple-package = {
          pkgs = [ agdapkg ];
        };
      })
  ];
}
