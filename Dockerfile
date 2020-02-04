FROM nixos/nix

ENV proj /proj
WORKDIR ${proj}
ADD . $proj

RUN nix-channel --add https://nixos.org/channels/nixos-18.09 nixpkgs
RUN nix-channel --update

RUN nix-env -i git
RUN nix-build

RUN cp -Lpr result /crypto