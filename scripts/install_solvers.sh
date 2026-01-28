#!/usr/bin/env bash
set -euo pipefail

echo "Usage: install_solvers.sh [DIR] [--old-releases]"

# Default directory is ../binaries
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd -P)"
DIR="$(realpath -m -- "${1:-$SCRIPT_DIR/../binaries}")"
mkdir -p "$DIR"

OLD_RELEASES=false
if [[ "${2:-}" == "--old-releases" ]]; then
    OLD_RELEASES=true
fi

NEW_PATH=""

install_z3() {
    local ver="4.15.4"
    local name="z3-4.15.4-x64-glibc-2.39"
    local zip="${name}.zip"
    local url="https://github.com/Z3Prover/z3/releases/download/z3-${ver}/${zip}"
    echo "Downloading Z3..."
    [ -f "$DIR/$zip" ] || curl -L "$url" -o "$DIR/$zip"
    echo "Extracting Z3..."
    unzip -o "$DIR/$zip" -d "$DIR"
    export NEW_PATH="$NEW_PATH:$DIR/$name/bin"
}

install_cvc5() {
    local ver="${1:-1.3.2}"
    local name="cvc5-Linux-x86_64-libcxx-static"
    local file="${name}.zip"
    local dir="cvc5-${ver}"
    echo "Downloading cvc5..."
    local url="https://github.com/cvc5/cvc5/releases/download/cvc5-${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting cvc5..."
    unzip -o "$DIR/$file" -d "$DIR/"
    mv "$DIR/$name" "$DIR/$dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir/bin"
}

install_cvc5_1.0.5() {
    local ver="1.0.5"
    local name="cvc5-Linux-Static"
    local file="${name}.zip"
    local dir="cvc5-${ver}"
    echo "Downloading old cvc5..."
    local url="https://github.com/cvc5/cvc5/releases/download/cvc5-${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting old cvc5..."
    unzip -o "$DIR/$file" -d "$DIR/$dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir"
}

install_opensmt() {
    local ver="${1:-2.9.2}"
    local file="opensmt-x64-linux-static.tar.bz2"
    local dir="opensmt-${ver}"
    mkdir -p "$DIR/$dir"
    echo "Downloading OpenSMT..."
    local url="https://github.com/usi-verification-and-security/opensmt/releases/download/v${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting OpenSMT..."
    tar -xjf "$DIR/$file" -C "$DIR/$dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir"
}

install_opensmt_2.5.0() {
    local ver="2.5.0"
    local file="opensmt-${ver}-x64-linux.tar.bz2"
    local dir="opensmt-${ver}"
    mkdir -p "$DIR/$dir"
    echo "Downloading OpenSMT..."
    local url="https://github.com/usi-verification-and-security/opensmt/releases/download/v${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting OpenSMT..."
    tar -xjf "$DIR/$file" -C "$DIR/$dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir"
}

install_golem() {
    local commit="50f3b1a"
    local dir="golem-${commit}"
    echo "Cloning Golem repository..."
    if [ ! -d "$DIR/$dir/.git" ]; then
        git clone https://github.com/usi-verification-and-security/golem.git "$DIR/$dir"
    else
        echo "Golem already present at $DIR/$dir"
    fi
    local prev_dir="$(pwd)"
    cd "$DIR/$dir"
    git checkout "$commit"
    mkdir -p build
    cd build
    echo "Building Golem..."
    cmake ..
    make -j4
    cd "$prev_dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir/build"
}

install_golem_release() {
    local ver="${1:-0.9.0}"
    local file="golem-x64-linux.tar.bz2"
    local dir="golem-${ver}"
    mkdir -p "$DIR/$dir"
    echo "Downloading Golem..."
    local url="https://github.com/usi-verification-and-security/golem/releases/download/v${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting Golem..."
    tar -xjf "$DIR/$file" -C "$DIR/$dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir"
}

install_golem_0.4.0() {
    local ver="0.4.0"
    local file="golem_${ver}-x64-linux.tar.bz2"
    local dir="golem-${ver}"
    mkdir -p "$DIR/$dir"
    echo "Downloading Golem..."
    local url="https://github.com/usi-verification-and-security/golem/releases/download/v${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting Golem..."
    tar -xjf "$DIR/$file" -C "$DIR/$dir"
    export NEW_PATH="$NEW_PATH:$DIR/$dir"
}

install_eldarica() {
    local ver="${1:-2.2.1}"
    local file="eldarica-bin-${ver}.zip"
    local dir="eldarica-${ver}"
    echo "Downloading Eldarica..."
    local url="https://github.com/uuverifiers/eldarica/releases/download/v${ver}/${file}"
    [ -f "$DIR/$file" ] || curl -L "$url" -o "$DIR/$file"
    echo "Extracting Eldarica..."
    unzip -o "$DIR/$file" -d "$DIR"
    export NEW_PATH="$NEW_PATH:$DIR/$dir"
}

install_carcara() {
    cargo install --git https://github.com/ufmg-smite/carcara.git --rev b685c15 
}

# if OLD_RELEASES is true, install older versions
if [ "$OLD_RELEASES" = true ]; then
    install_cvc5_1.0.5
    install_opensmt_2.5.0
    install_golem_0.4.0
    install_golem_release "0.9.0"
    install_eldarica "2.0.9"
    exit 0
fi

install_z3
install_cvc5 
install_opensmt
install_golem
install_eldarica
install_carcara

echo "export PATH=\"$NEW_PATH:\$PATH\"" > env.sh
