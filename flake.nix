{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      coqPackages = pkgs.coqPackages;
    in
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          coq
          coqPackages.stdpp
          coqPackages.iris
        ];

        shellHook = ''
          export COQPATH="${coqPackages.stdpp}/lib/coq/${pkgs.coq.coq-version}/user-contrib/:${coqPackages.iris}/lib/coq/${pkgs.coq.coq-version}/user-contrib/"
        '';
      };
    });
}
