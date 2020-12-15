#!/usr/bin/env bash
set -Eeuxo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=$(pwd)/bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(find "${3:-dist-newstyle}" -type f -name "$1$EXT")"
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
    is_exe "dist/bin" "saw" && is_exe "dist/bin" "saw-remote-api" && return
  else
    is_exe "dist/bin" "saw" && is_exe "dist/bin" "saw-remote-api" && is_exe "dist/bin" "jss" && return
    extract_exe "jss" "dist/bin"
  fi
  extract_exe "saw" "dist/bin"
  extract_exe "saw-remote-api" "dist/bin"
  export PATH=$PWD/dist/bin:$PATH
  echo "$PWD/dist/bin" >> "$GITHUB_PATH"
  strip dist/bin/saw* || echo "Strip failed: Ignoring harmless error"
  strip dist/bin/jss* || echo "Strip failed: Ignoring harmless error"
}

install_z3() {
  is_exe "$BIN" "z3" && return

  case "$RUNNER_OS" in
    Linux) file="ubuntu-16.04.zip" ;;
    macOS) file="osx-10.14.6.zip" ;;
    Windows) file="win.zip" ;;
  esac
  curl -o z3.zip -sL "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/z3-$Z3_VERSION-x64-$file"

  if $IS_WIN; then 7z x -bd z3.zip; else unzip z3.zip; fi
  cp z3-*/bin/z3$EXT $BIN/z3$EXT
  $IS_WIN || chmod +x $BIN/z3
  rm z3.zip
}

install_cvc4() {
  is_exe "$BIN" "cvc4" && return
  version="${CVC4_VERSION#4.}" # 4.y.z -> y.z

  case "$RUNNER_OS" in
    Linux) file="x86_64-linux-opt" ;;
    Windows) file="win64-opt.exe" ;;
    macOS) file="macos-opt" ;;
  esac
  # Temporary workaround
  if [[ "$RUNNER_OS" == "Linux" ]]; then
    curl -o cvc4$EXT -sL "https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/cvc4-2020-08-18-x86_64-linux-opt"
  else
    curl -o cvc4$EXT -sL "https://github.com/CVC4/CVC4/releases/download/$version/cvc4-$version-$file"
  fi
  $IS_WIN || chmod +x cvc4$EXT
  mv cvc4$EXT "$BIN/cvc4$EXT"
}

install_yices() {
  is_exe "$BIN" "yices" && return
  ext=".tar.gz"
  case "$RUNNER_OS" in
    Linux) file="pc-linux-gnu-static-gmp.tar.gz" ;;
    macOS) file="apple-darwin18.7.0-static-gmp.tar.gz" ;;
    Windows) file="pc-mingw32-static-gmp.zip" && ext=".zip" ;;
  esac
  curl -o "yices$ext" -sL "https://yices.csl.sri.com/releases/$YICES_VERSION/yices-$YICES_VERSION-x86_64-$file"

  if $IS_WIN; then
    7z x -bd "yices$ext"
    mv "yices-$YICES_VERSION"/bin/*.exe "$BIN"
  else
    tar -xzf "yices$ext"
    pushd "yices-$YICES_VERSION" || exit
    sudo ./install-yices
    popd || exit
  fi
  rm -rf "yices$ext" "yices-$YICES_VERSION"
}

install_yasm() {
  is_exe "$BIN" "yasm" && return
  case "$RUNNER_OS" in
    Linux) sudo apt-get update -q && sudo apt-get install -y yasm ;;
    macOS) brew install yasm ;;
    Windows) choco install yasm ;;
  esac
}

build() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  echo "allow-newer: all" >> cabal.project.local
  pkgs=(saw saw-remote-api)
  if $IS_WIN; then
    echo "flags: -builtin-abc" >> cabal.project.local
    echo "constraints: jvm-verifier -builtin-abc, cryptol-saw-core -build-css" >> cabal.project.local
  else
    pkgs+=(jss)
  fi
  echo "allow-newer: all" >> cabal.project.local
  tee -a cabal.project > /dev/null < cabal.project.ci
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

build_abc() {
  arch=X86_64
  case "$RUNNER_OS" in
    Linux) os="Linux" ;;
    macOS) os="OSX" ;;
    Windows) return ;;
  esac
  pushd deps/abcBridge
  $IS_WIN || scripts/build-abc.sh $arch $os
  cp abc-build/abc $BIN/abc
  popd
}

install_system_deps() {
  install_z3 &
  install_cvc4 &
  install_yices &
  install_yasm &
  wait
  export PATH=$PWD/$BIN:$PATH
  echo "$PWD/$BIN" >> "$GITHUB_PATH"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" yices && is_exe "$BIN" yasm
}

test_dist() {
  find_java
  pushd intTests
  for t in test0001 test0019_jss_switch_statement test_crucible_jvm test_ecdsa test_examples test_issue108 test_tutorial1 test_tutorial2 test_tutorial_w4; do echo $t >> disabled_tests.txt; done
  LOUD=true ./runtests.sh
  sh -c "! grep '<failure>' results.xml"
}

build_cryptol() {
  is_exe "dist/bin" "cryptol" && return
  pushd deps/cryptol
  git submodule update --init
  .github/ci.sh build
  popd
}

bundle_files() {
  mkdir -p dist dist/{bin,doc,examples,include,lib}

  cp deps/abcBridge/abc-build/copyright.txt dist/ABC_LICENSE
  cp LICENSE README.md dist/
  $IS_WIN || chmod +x dist/bin/*

  cp doc/extcore.md dist/doc
  cp doc/tutorial/sawScriptTutorial.pdf dist/doc/tutorial.pdf
  cp doc/manual/manual.pdf dist/doc/manual.pdf
  cp -r doc/tutorial/code dist/doc
  cp deps/jvm-verifier/support/galois.jar dist/lib
  cp -r deps/cryptol/lib/* dist/lib
  cp -r examples/* dist/examples
}

find_java() {
  pushd .github
  javac PropertiesTest.java
  RT_JAR="$(java PropertiesTest | tr : '\n' | grep rt.jar | head -n 1)"
  export RT_JAR
  echo "RT_JAR=$RT_JAR" >> "$GITHUB_ENV"
  rm PropertiesTest.class
  popd
}

sign() {
  gpg --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep galois -a1 | head -n1 | awk '{$1=$1};1')"
  echo "$fingerprint:6" | gpg --import-ownertrust
  gpg --yes --no-tty --batch --pinentry-mode loopback --default-key "$fingerprint" --detach-sign -o "$1".sig --passphrase-file <(echo "$SIGNING_PASSPHRASE") "$1"
}

zip_dist() {
  : "${VERSION?VERSION is required as an environment variable}"
  name="${name:-"saw-$VERSION-$RUNNER_OS-x86_64"}"
  mv dist "$name"
  tar -czf "$name".tar.gz "$name"
  sign "$name".tar.gz
  [[ -f "$name".tar.gz.sig ]] && [[ -f "$name".tar.gz ]]
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
