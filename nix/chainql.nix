{
  lib,
  stdenv,
  craneLib,
  static ? false,
}: let
  inherit (stdenv.hostPlatform) system;
in
  craneLib.buildPackage {
    src = craneLib.cleanCargoSource ../.;
    strictDeps = true;
    env = lib.optionalAttrs static {
      CARGO_BUILD_TARGET =
        if system == "x86_64-linux"
        then "x86_64-unknown-linux-musl"
        else throw "static only supported for x86_64-linux";
    };
  }
