let
  nixpkgs = import <nixpkgs> {};
  nixos-15 = import <nixos-15> {};
in
nixpkgs.agda.mkDerivation (self: {
  name = "cripto";
  src = ./.;
  everythingFile = " --js ./src/Everything.agda";
  buildDepends = [ nixos-15.agdaPrelude ];
})
