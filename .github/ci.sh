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
  # Configure with --disable-documentation and --haddock-internal so
  # that the haddock run later, if enabled, doesn't recompile the
  # world by using those flags. (See haddock() below for discussion of
  # why those flags are used.) We could do this only for builds where
  # we're intending to do the haddock run, but it should have no
  # effect otherwise and unconditional is simpler.
  cabal v2-configure -j --enable-tests --disable-documentation --haddock-internal
  git status --porcelain
  if $IS_WIN; then
    pkgs=(saw crux-mir-comp)
  else
    pkgs=(saw crux-mir-comp saw-remote-api)
  fi
  cat cabal.project.ci >> cabal.project.local
  if [[ "$ENABLE_HPC" == "true" ]]; then
    cat cabal.project.ci-hpc >> cabal.project.local
  fi
  # In the distant past, we had to retry the `cabal build` command to work
  # around issues with caching dylib files on macOS. These issues appear to
  # be less likely with modern GitHub Actions caching, so we have removed the
  # retry logic.
  cabal v2-build "$@" "${pkgs[@]}"
}

haddock() {
  # It seems that the secret sauce for getting cabal to _not_ go
  # through building docs for every single sublibrary is to pass
  # --disable-documentation, counterintuitive though that is.
  #
  # Note: there's a v2-haddock-project that runs haddock on all
  # packages in the project, which would avoid needing to list them
  # out. However, it doesn't support the --disable-documentation
  # option, so it won't currently serve. (Also for some reason it
  # currently demands --internal in place of --haddock-internal.)
  #
  # We use --haddock-internal because the point of generating the
  # haddocks for SAW (which doesn't have an external-facing library
  # interface) is to serve as an internals reference.
  local PACKAGES='
    rme
    saw-core
    cryptol-saw-core
    saw-core-what4
    saw-core-sbv
    saw-core-aig
    saw-core-coq
    heapster-saw
    saw-script
    saw-remote-api
    crucible-mir-comp
    crux-mir-comp
    verif-viewer
  '
  cabal v2-haddock --haddock-internal --disable-documentation $PACKAGES
}

# Gather and tar up all HPC coverage files and binaries
collect_hpc_files() {
  local MIX_FILES=$(find dist-newstyle -name "*.mix")
  local GENERATED_HS_FILES=$(find dist-newstyle/build -name "*.hs")
  local BINS="dist/bin"
  tar cvf hpc.tar.gz ${MIX_FILES} ${GENERATED_HS_FILES} ${BINS}
}

# Download HTML coverage reports and generate an index file linking to them
collect_all_html() {
  local HTML_DIR=all-html
  mkdir -p ${HTML_DIR}
  (cd ${HTML_DIR} && gh run download -p "coverage-html-*" && python3 ../.github/generate_index.py)
}

install_system_deps() {
  (cd $BIN && curl -o bins.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BUILD_TARGET_OS-$BUILD_TARGET_ARCH-bin.zip" && unzip -o bins.zip && rm bins.zip)
  chmod +x $BIN/*
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  export PATH="$BIN:$PATH"
  echo "$BIN" >> "$GITHUB_PATH"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" cvc5 && is_exe "$BIN" yices && is_exe "$BIN" bitwuzla && is_exe "$BIN" boolector
}

build_cryptol() {
  cabal build exe:cryptol
}

bundle_files() {
  mkdir -p dist dist/{bin,deps,doc,examples,include,lib}
  mkdir -p dist/doc/{llvm-java-verification-with-saw,rust-verification-with-saw,saw-user-manual}

  cp LICENSE README.md dist/
  $IS_WIN || chmod +x dist/bin/*

  (cd deps/cryptol-specs && git archive --prefix=cryptol-specs/ --format=tar HEAD) | (cd dist/deps && tar x)
  cp doc/pdfs/llvm-java-verification-with-saw.pdf dist/doc/llvm-java-verification-with-saw
  cp doc/pdfs/rust-verification-with-saw.pdf dist/doc/rust-verification-with-saw
  cp doc/pdfs/saw-user-manual.pdf dist/doc/saw-user-manual
  cp -r doc/llvm-java-verification-with-saw/code dist/doc/llvm-java-verification-with-saw
  cp -r doc/rust-verification-with-saw/code dist/doc/rust-verification-with-saw
  cp intTests/jars/galois.jar dist/lib
  cp -r deps/cryptol/lib/* dist/lib
  cp -r examples/* dist/examples
}

sign() {
  # This is surrounded with `set +x; ...; set -x` to disable printing out
  # statements that could leak GPG-related secrets.
  set +x
  gpg --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep Galois -a1 | head -n1 | awk '{$1=$1};1')"
  echo "$fingerprint:6" | gpg --import-ownertrust
  gpg --yes --no-tty --batch --pinentry-mode loopback --default-key "$fingerprint" --detach-sign -o "$1".sig --passphrase-file <(echo "$SIGNING_PASSPHRASE") "$1"
  set -x
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
  cp "$BIN/bitwuzla"   dist/bin/
  cp "$BIN/boolector"  dist/bin/
  cp "$BIN/cvc4"       dist/bin/
  cp "$BIN/cvc5"       dist/bin/
  cp "$BIN/yices"      dist/bin/
  cp "$BIN/yices-smt2" dist/bin/
  # Z3 4.8.14 has been known to nondeterministically time out with the AWSLC
  # and BLST proofs, so we include both 4.8.8 and 4.8.14 so that we can fall
  # back to 4.8.8 (a version known to work with the AWSLC and BLST proofs)
  # where necessary. See #1772.
  cp "$BIN/z3"         dist/bin/
  cp "$BIN/z3-4.8.8"   dist/bin/
  cp "$BIN/z3-4.8.14"  dist/bin/
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
