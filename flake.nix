# Based on https://github.com/cdepillabout/coq-playground
{
  description = "Coq Playground";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-21.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlay = self: _: {
          software-foundations-shell = self.stdenv.mkDerivation {
            name = "coq-playground-shell";
            dontUnpack = true;
            nativeBuildInputs = [
              self.coq_8_13
            ];
          };
        };
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            overlay
          ];
        };
      in
      {
        devShell = pkgs.software-foundations-shell;
      }
    );
}
