{
  description = "Master thesis of cryptocurrency in Agda";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.nixos-18 = {
    url = github:NixOS/nixpkgs/nixos-18.09;
    flake = false;
  };

  outputs = { self, flake-utils, nixpkgs, nixos-18 }:
    flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
        nixos18 = import nixos-18 { inherit system; };
    in rec {
      packages.thesis = with pkgs;
        let agdapkg = nixos18.callPackage src/default.nix {};
            ghcPackages = ghc.withPackages (pkgs: with pkgs; [ shake ]);
        in stdenv.mkDerivation {
            name = "master-thesis";
            src = ./.;
            buildInputs = [
              which
              ghcPackages
              (texlive.combine {
                  inherit (texlive)
                    scheme-full
                  ;
                  simple-package = {
                    pkgs = [ agdapkg ];
                  };
                })
            ];
            buildPhase = ''shake'';
            installPhase = ''cp -r _build $out'';
          };
      defaultPackage = packages.thesis;
    });
}
