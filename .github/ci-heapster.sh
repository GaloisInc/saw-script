#!/usr/bin/env bash
set -Eeuxo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
[[ "$RUNNER_OS" == 'macOS' ]] && IS_MACOS=true || IS_MACOS=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(cabal v2-exec which "$1$EXT")"
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
  is_exe "dist/bin" "saw" && is_exe "dist/bin" "jss" && return
  extract_exe "saw" "dist/bin"
  extract_exe "jss" "dist/bin"
  export PATH=$PWD/dist/bin:$PATH
  echo "$PWD/dist/bin" >> $GITHUB_PATH
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
  if [[ "$RUNNER_OS" = "Linux" ]]; then
    sudo apt-get update -q && sudo apt-get install -y yasm
  else
    brew install yasm
  fi
}

build() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  cabal v2-configure -j2 --minimize-conflict-set
  # Workaround for https://github.com/GaloisInc/abcBridge/issues/15
  if $IS_MACOS; then
    echo "flags: -builtin-abc" >> cabal.project.local
    echo "constraints: jvm-verifier -builtin-abc" >> cabal.project.local
  fi
  if ! retry cabal v2-build "$@" saw jss; then
    if [[ "$RUNNER_OS" == "macOS" ]]; then
      echo "Working around a dylib issue on macos by removing the cache and trying again"
      cabal v2-clean
      retry cabal v2-build "$@" saw jss
    else
      exit 1
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
  popd
}

install_system_deps() {
  install_z3 &
  install_cvc4 &
  install_yices &
  install_yasm &
  wait
  export PATH=$PWD/$BIN:$PATH
  echo "$PWD/$BIN" >> $GITHUB_PATH
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" yices && is_exe "$BIN" yasm
}

COMMAND="$1"
shift

"$COMMAND" "$@"
