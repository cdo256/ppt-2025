{
  description = "COMP4078: Programs, Proofs and Types";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    just-agda.url = "github:cdo256/just-agda";
  };

  outputs =
    {
      self,
      nixpkgs,
      just-agda,
    }:
    let
      systems = [ "x86_64-linux" ];
      forEachSystem = fn: nixpkgs.lib.genAttrs systems (system: fn nixpkgs.legacyPackages.${system});
    in
    {
      packages = forEachSystem (pkgs: {
        default = just-agda.packages.${pkgs.system}.default;
      });
      devShells = forEachSystem (pkgs: {
        default = pkgs.mkShell {
          buildInputs = [
            just-agda.packages.${pkgs.system}.default
          ];
        };
      });
    };
}
