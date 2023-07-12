{
  description = "chainql";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };
  outputs = { nixpkgs, flake-utils, rust-overlay, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlay ];
        };
        rust = ((pkgs.rustChannelOf { date = "2022-11-20"; channel = "nightly"; }).default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
          targets = ["x86_64-unknown-linux-musl" "x86_64-unknown-linux-gnu"];
        });
      in
      rec {
        devShell = pkgs.mkShell {
          nativeBuildInputs = with pkgs;[
            rust
            cargo-edit
          ];
        };
      }
    );
}
