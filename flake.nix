{
  description = "A development environment for Lean 4 using elan and VS Code.";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };
  outputs = { self, nixpkgs, ... }:
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
        in
        pkgs.mkShell {
          buildInputs = with pkgs; [
            lean4
            elan
            vscode
          ];

          shellHook = ''
            echo "Entering Nix shell with Lean 4, Elan, and VS Code..."
          '';
        };
    in
    {
      devShells = forAllSystems (system: {
        default = mkShellFor system;
      });
    };
}
