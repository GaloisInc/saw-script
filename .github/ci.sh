#!/usr/bin/env bash
set -Eeuxo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=$(pwd)/bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(find "${3:-dist-newstyle}" -type f -name "$1$EXT" | sort -g | tail -1)"
  name="$(basename "$exe")"
  echo "Copying $name to $2"
  mkdir -p "$2"
  cp -f "$exe" "$2/$name"
  $IS_WIN || chmod +x "$2/$name"
}

retry() {
  echo "Attempting with retry:" "$@"
  local n=1
  while true; do
    if "$@"; then
      break
    else
      if [[ $n -lt 3 ]]; then
        sleep $n # don't retry immediately
        ((n++))
        echo "Command failed. Attempt $n/3:"
      else
        echo "The command has failed after $n attempts."
        return 1
      fi
    fi
  done
}

setup_dist_bins() {
  if $IS_WIN; then
    is_exe "dist/bin" "saw" && return
  else
    is_exe "dist/bin" "saw" && is_exe "dist/bin" "saw-remote-api" && return
    extract_exe "saw-remote-api" "dist/bin"
  fi
  extract_exe "saw" "dist/bin"
  extract_exe "cryptol" "dist/bin"
  export PATH=$PWD/dist/bin:$PATH
  echo "$PWD/dist/bin" >> "$GITHUB_PATH"
  strip dist/bin/saw* || echo "Strip failed: Ignoring harmless error"
}

build() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  cabal v2-configure -j --enable-tests
  git status --porcelain
  if $IS_WIN; then
    pkgs=(saw crux-mir-comp)
  else
    pkgs=(saw crux-mir-comp saw-remote-api)
  fi
  tee -a cabal.project.local > /dev/null < cabal.project.ci
  if ! retry cabal v2-build "$@" "${pkgs[@]}"; then
    if [[ "$RUNNER_OS" == "macOS" ]]; then
      echo "Working around a dylib issue on macos by removing the cache and trying again"
      cabal v2-clean
      retry cabal v2-build "$@" "${pkgs[@]}"
    else
      return 1
    fi
  fi
}

install_system_deps() {
  (cd $BIN && curl -o bins.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BUILD_TARGET_OS-bin.zip" && unzip -o bins.zip && rm bins.zip)
  chmod +x $BIN/*
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  export PATH="$BIN:$PATH"
  echo "$BIN" >> "$GITHUB_PATH"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" yices
}

build_cryptol() {
  cabal build exe:cryptol
}

bundle_files() {
  mkdir -p dist dist/{bin,deps,doc,examples,include,lib}

  cp LICENSE README.md dist/
  $IS_WIN || chmod +x dist/bin/*

  (cd deps/cryptol-specs && git archive --prefix=cryptol-specs/ --format=tar HEAD) | (cd dist/deps && tar x)
  cp doc/extcore.md dist/doc
  cp doc/tutorial/sawScriptTutorial.pdf dist/doc/tutorial.pdf
  cp doc/manual/manual.pdf dist/doc/manual.pdf
  cp -r doc/tutorial/code dist/doc
  cp intTests/jars/galois.jar dist/lib
  cp -r deps/cryptol/lib/* dist/lib
  cp -r examples/* dist/examples
}

sign() {
  gpg --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep galois -a1 | head -n1 | awk '{$1=$1};1')"
  echo "$fingerprint:6" | gpg --import-ownertrust
  gpg --yes --no-tty --batch --pinentry-mode loopback --default-key "$fingerprint" --detach-sign -o "$1".sig --passphrase-file <(echo "$SIGNING_PASSPHRASE") "$1"
}

zip_dist() {
  name="$1"
  cp -r dist "$name"
  tar -czf "$name".tar.gz "$name"
}

zip_dist_with_solvers() {
  sname="${1}"
  # Because these binaries come from the what4-solvers repository, they
  # should be at least as portable (in terms of dynamic library
  # dependencies) as the SAW binaries.
  cp "$BIN/abc"        dist/bin/
  cp "$BIN/cvc4"       dist/bin/
  cp "$BIN/yices"      dist/bin/
  cp "$BIN/yices-smt2" dist/bin/
  cp "$BIN/z3"         dist/bin/
  cp -r dist "$sname"
  tar -cvzf "$sname".tar.gz "$sname"
}

output() { echo "::set-output name=$1::$2"; }
ver() { grep Version saw-script.cabal | awk '{print $2}'; }
set_version() { output saw-version "$(ver)"; }
set_files() { output changed-files "$(files_since "$1" "$2")"; }
files_since() {
  changed_since="$(git log -1 --before="@{$2}")"
  files="${changed_since:+"$(git diff-tree --no-commit-id --name-only -r "$1" | xargs)"}"
  echo "$files"
}

COMMAND="$1"
shift

"$COMMAND" "$@"
