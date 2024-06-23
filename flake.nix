{
  description = "chainql";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    shelly = {
      url = "github:CertainLach/shelly";
      inputs.flake-parts.follows = "flake-parts";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = inputs @ {
    nixpkgs,
    rust-overlay,
    flake-parts,
    crane,
    shelly,
    ...
  }: let
    inherit (nixpkgs) lib;
  in
    flake-parts.lib.mkFlake {inherit inputs;} {
      imports = [shelly.flakeModule];
      systems = lib.systems.flakeExposed;
      perSystem = {
        pkgs,
        system,
        ...
      }: let
        rust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
        craneLib = (crane.mkLib pkgs).overrideToolchain rust;
      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [rust-overlay.overlays.default];
        };
        packages = rec {
          default = chainql;
          chainql = pkgs.callPackage ./nix/chainql.nix {inherit craneLib;};
          chainql-static = chainql.override {static = true;};
        };
        shelly.shells.default = {
          factory = craneLib.devShell;
          packages = with pkgs; [
            cargo-edit
            rustPlatform.bindgenHook
          ];

          environment.PROTOC = "${pkgs.protobuf}/bin/protoc";
        };
      };
    };
}
