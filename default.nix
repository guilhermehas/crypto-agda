{ pkgs ? import <nixpkgs> {} }: with pkgs;

let
  agdapkg = (import src/default.nix) {};
in
stdenv.mkDerivation {
  name = "qualificacao-mestrado";
  src = ./.;
  buildInputs = [
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
