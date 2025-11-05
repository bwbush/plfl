{
  description = "A development environment for Lean 4 using elan and VS Code.";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nixpkgs2405.url = "github:NixOS/nixpkgs/nixos-24.05";
  };
  outputs = { self, nixpkgs, nixpkgs2405, ... }:
    let
      supportedSystems = [ "x86_64-linux"  ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      mkShellFor = system:
        let
          pkgs = import nixpkgs { 
            inherit system; 
            config = { 
              allowUnfree = true;
            }; 
          };
          pkgs2405 = nixpkgs2405.legacyPackages.${system};
          ghc = pkgs2405.haskellPackages.ghcWithPackages (p: with p; [ ieee754 ]);
          haskellPkgs = with pkgs2405.haskellPackages; [
            ghc
            cabal-install
            haskell-language-server
          ];
          agda-stdlib = pkgs2405.agdaPackages.standard-library.overrideAttrs (oldAtts: rec {
            version = "2.1";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "v${version}";
              sha256 = "sha256-tv/Fj8ZJgSvieNLlXBjyIR7MSmDp0e2QbN1d/0xBpFg=";
            };
          });
          agdaPkgs = [
            (pkgs2405.agda.withPackages (ps: [
              agda-stdlib
            ]))
          ];
          emacsPkgs = (pkgs2405.emacs.pkgs.withPackages (epkgs: (with epkgs.melpaStablePackages; [
            epkgs.agda2-mode
          ])));
        in
        pkgs.mkShell {
          buildInputs = with pkgs; [
            lean4
            elan
            ghc
            haskellPkgs
            agdaPkgs
            emacsPkgs
            vscode
          ];
          shellHook = ''
            echo "Entering Nix shell with Lean, Agda, and VS Code..."
          '';
        };
    in
    {
      devShells = forAllSystems (system: {
        default = mkShellFor system;
      });
    };
}
