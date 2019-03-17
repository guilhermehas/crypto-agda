let
  nixos-15 = import <nixos-15> {};
in
nixos-15.agda.mkDerivation (self: {
  name = "cripto";
  src = ./.;
  everythingFile = " --js ./src/Everything.agda";
  buildDepends = [ nixos-15.agdaPrelude ];
})
