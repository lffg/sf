{ pkgs ? import <nixpkgs> { } }:
pkgs.mkShell {
  name = "software-foundations";
  packages = with pkgs; [ coq_8_13 ];
}
