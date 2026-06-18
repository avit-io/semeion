{
  description = "semeion — intrinsic geometry of SRE signals in Agda";

  inputs = {
    nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/0.2511.912939";
    piforge = {
      url   = "github:avit-io/piforge";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    prometea = {
      url   = "github:avit-io/prometea";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.piforge.follows = "piforge";
    };
  };

  outputs = { self, nixpkgs, piforge, prometea }:
    let
      system = "x86_64-linux";
      pkgs   = nixpkgs.legacyPackages.${system};

      semeionLib = pkgs.stdenv.mkDerivation {
        name      = "semeion-agda-lib";
        src       = builtins.path { path = ./.; name = "semeion-src"; };
        dontBuild = true;
        installPhase = ''
          mkdir -p $out
          cp -r Semeion $out/
          printf 'name: semeion\ninclude: .\ndepend: standard-library prometea\n' \
            > $out/semeion.agda-lib
        '';
      };

      # Sentinel sul nix store path: invalida la cache quando la lib cambia.
      copySemeion = ''
        _semeion="$_cache/semeion"
        _semeion_tag="${semeionLib}"
        if [ ! -f "$_semeion/.nix-tag" ] || [ "$(cat "$_semeion/.nix-tag")" != "$_semeion_tag" ]; then
          echo "semeion: copying library to $_semeion..." >&2
          rm -rf "$_semeion"
          mkdir -p "$_semeion"
          cp -r ${semeionLib}/. "$_semeion/"
          chmod -R u+w "$_semeion"
          printf 'name: semeion\ninclude: .\ndepend: standard-library prometea\n' \
            > "$_semeion/semeion.agda-lib"
          echo "$_semeion_tag" > "$_semeion/.nix-tag"
        fi
      '';

    in
    {
      packages.${system} = {
        lib     = semeionLib;
        default = semeionLib;
      };

      # Dev shell per sviluppare semeion: stdlib + prometea in AGDA_DIR.
      # prometea.lib.mkShell esporta $_cache / $_stdlib / $_prometea nel hook.
      devShells.${system}.default = prometea.lib.mkShell {
        inherit pkgs;
        extraPackages = with pkgs; [ watchexec ];
        shellHook = ''
          mkdir -p "$_cache/semeion-dev"
          printf '%s\n%s\n' \
            "$_stdlib/standard-library.agda-lib" \
            "$_prometea/prometea.agda-lib" \
            > "$_cache/semeion-dev/libraries"
          export AGDA_DIR="$_cache/semeion-dev"
        '';
      };

      # Per i consumer (Penelope a valle): stdlib + prometea + semeion.
      lib.mkShell = { pkgs, extraPackages ? [], shellHook ? "" }:
        prometea.lib.mkShell {
          inherit pkgs extraPackages;
          shellHook = copySemeion + ''
            mkdir -p "$_cache/semeion-env"
            printf '%s\n%s\n%s\n' \
              "$_stdlib/standard-library.agda-lib" \
              "$_prometea/prometea.agda-lib" \
              "$_semeion/semeion.agda-lib" \
              > "$_cache/semeion-env/libraries"
            export AGDA_DIR="$_cache/semeion-env"
          '' + shellHook;
        };
    };
}
