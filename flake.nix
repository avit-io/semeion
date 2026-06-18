{
  description = "semeion — intrinsic geometry of SRE signals in Agda";

  inputs = {
    nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/0.2511.912939";
    piforge = {
      url   = "github:avit-io/piforge";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, piforge }:
    let
      system   = "x86_64-linux";
      pkgs     = nixpkgs.legacyPackages.${system};
      stdlib28 = piforge.packages.${system}."stdlib-28";

      semeionLib = pkgs.stdenv.mkDerivation {
        name      = "semeion-agda-lib";
        src       = builtins.path { path = ./.; name = "semeion-src"; };
        dontBuild = true;
        installPhase = ''
          mkdir -p $out
          cp -r Semeion $out/
          printf 'name: semeion\ninclude: .\ndepend: standard-library\n' \
            > $out/semeion.agda-lib
        '';
      };

      # semeion è una RADICE: solo standard-library. Apeiron dei segnali.
      copyStdlib = ''
        _cache="''${XDG_CACHE_HOME:-$HOME/.cache}/piforge"
        _stdlib="$_cache/stdlib-2.3"
        if [ ! -d "$_stdlib" ]; then
          echo "semeion: copying stdlib 2.3 to $_stdlib (one-time setup)..." >&2
          mkdir -p "$_stdlib"
          cp -r ${stdlib28}/. "$_stdlib/"
          chmod -R u+w "$_stdlib"
        fi
      '';

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
          printf 'name: semeion\ninclude: .\ndepend: standard-library\n' \
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

      # Dev shell per sviluppare semeion: solo stdlib in AGDA_DIR.
      devShells.${system}.default = piforge.lib.agda.mkShell {
        inherit pkgs;
        version             = "v28";
        useRuntimeLibraries = true;
        extraPackages       = with pkgs; [ watchexec ];
        shellHook           = copyStdlib + ''
          mkdir -p "$_cache/semeion-dev"
          printf '%s\n' "$_stdlib/standard-library.agda-lib" \
            > "$_cache/semeion-dev/libraries"
          export AGDA_DIR="$_cache/semeion-dev"
        '';
      };

      # Per i consumer (Penelope a valle): stdlib + semeion.
      lib.mkShell = { pkgs, extraPackages ? [], shellHook ? "" }:
        piforge.lib.agda.mkShell {
          inherit pkgs;
          version             = "v28";
          useRuntimeLibraries = true;
          inherit extraPackages;
          shellHook = copyStdlib + copySemeion + ''
            mkdir -p "$_cache/semeion-env"
            printf '%s\n%s\n' \
              "$_stdlib/standard-library.agda-lib" \
              "$_semeion/semeion.agda-lib" \
              > "$_cache/semeion-env/libraries"
            export AGDA_DIR="$_cache/semeion-env"
          '' + shellHook;
        };
    };
}
