{
  description = "A flake for building Hello World";

  inputs.nixos-18 = {
    url = github:NixOS/nixpkgs/nixos-18.09;
    flake = false;
  };

  outputs = { self, nixpkgs, nixos-18 }: {
    defaultPackage.x86_64-linux = import ./default.nix {
      pkgs = import nixpkgs { system = "x86_64-linux"; };
      nixos-18 = import nixos-18 { system = "x86_64-linux"; };
    };
  };
}
