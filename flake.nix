{
  description = "COMP4078: Programs, Proofs and Types";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    #cornelis.url = "github:agda/cornelis";
    #cornelis.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    {
      self,
      nixpkgs,
    }:
    let
      pkgs = import nixpkgs {
        system = "x86_64-linux";
        overlays = [
          #cornelis.overlays.cornelis
          (self: super: {
            haskellPackages = super.haskellPackages.override {
              overrides = self: super: {
                Agda = super.Agda.overrideAttrs (oldAttrs: {
                  separateDebugInfo = true;
                });
              };
            };
          })
        ];
      };
      texlive = pkgs.texliveFull.withPackages (ps: [
        ps.latexmk
        ps.pgf # TikZ
        pkgs.inkscape
        #ps.luatex
      ]);

      agda = pkgs.agda.withPackages (ps: [
        ps.standard-library
      ]);
    in
    {
      packages.x86_64-linux.agda = agda;

      devShells.x86_64-linux.default = pkgs.mkShell {
        buildInputs = [
          agda
          texlive
          #cornelis.x86_64-linux.packages.cornelis
          #pkgs.haskellPackages.ghci_8_10_2
          #pkgs.ghc
        ];
      };
    };
}
