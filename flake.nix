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
        in stdenv.mkDerivation {
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
          };
      defaultPackage = packages.thesis;
    });
}
