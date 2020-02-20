{ pkgs ? import <nixpkgs> {} }: with pkgs;

let
  prelude =
    agda.mkDerivation (self: rec {
      version = "d193a94bfac9505148cb5cd1b68d08a08260b59c";
      name = "agda-prelude-${version}";

      src = fetchGit {
        url = "https://github.com/UlfNorell/agda-prelude.git";
        rev = version;
      };

      topSourceDirectories = [ "src" ];
      everythingFile = "src/Prelude.agda";

      meta = with stdenv.lib; {
        homepage = https://github.com/UlfNorell/agda-prelude;
        description = "Programming library for Agda";
        license = stdenv.lib.licenses.mit;
        platforms = stdenv.lib.platforms.unix;
        maintainers = with maintainers; [ fuuzetsu mudri ];
      };
    });
in
stdenv.mkDerivation rec {
  name = "agdapkg";
  src = ./.;
  pname = name;
  tlType = "run";
  buildInputs = [ haskellPackages.Agda prelude texlive.combined.scheme-basic ];
  configurePhase = ''
     export PRELUDE=${prelude}
  '';
}
