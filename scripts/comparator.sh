#!/usr/bin/env bash
# Run Comparator on this project, on a Linux machine (written for Ubuntu 24.04, x86_64 or
# arm64, at least 128 GB of memory and 300 GB of disk). Run it from the project root, as a
# normal user who can use sudo, in this order:
#
#   scripts/comparator.sh setup        # system packages and limits, Lean, challenge export,
#                                      # Mathlib cache, cache of the proof, build
#   scripts/comparator.sh companions   # short run: the three theorems that need Mathlib only
#   scripts/comparator.sh full         # long run: all four theorems (hours to days)
#
# Both runs pass `--paranoid`: besides Lean's own kernel, every external checker bundled
# with Lean has to accept the solution.
#
# Comparator judges exports: `challenge.export` is made from RH/Challenge.lean before
# anything of the proof is downloaded, `solution.export` from the compiled solution. Lean's
# kernel replays every declaration of the solution export, so the verdict does not rest on
# the prebuilt cache the solution is loaded from.
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
JUDGE="${JUDGE:-$HOME/rh-judge}"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

targets() {  # the kernel's built-in names, the permitted axioms, then the given theorems
  echo "$(sed -n 1p export-targets.txt) $(sed -n 3p export-targets.txt) $(sed -n 4p export-targets.txt) $*"
}
ALL="RH.reals_exist RH.zeta_exists RH.zeta_unique RH.riemann_hypothesis"
COMPANIONS="RH.reals_exist RH.zeta_exists RH.zeta_unique"

limits() {
  # Importing the proof maps several files for each of about 150,000 modules.
  sudo sysctl -w vm.max_map_count=8000000 fs.file-max=4000000 >/dev/null
  # Ubuntu 24.04 forbids the unprivileged user namespaces that bubblewrap needs.
  sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0 >/dev/null 2>&1 || true
  ulimit -n "$(ulimit -Hn)"
}

judge() {  # judge <config> <solution export> <log name>
  mkdir -p "$JUDGE/run"
  cp "$ROOT/lean-toolchain" "$ROOT/$1" "$JUDGE/run/"
  cd "$JUDGE/run"
  # The allocator setting only makes full-heap collections rarer; it changes nothing about
  # what the kernel checks.
  MIMALLOC_GENERIC_COLLECT=1000000 lake comparator --paranoid --config "$1" \
    --challenge-from-export "$JUDGE/challenge.export" \
    --solution-from-export "$2" 2>&1 | tee "$JUDGE/$3.log"
}

case "${1:-}" in
  setup)
    sudo apt-get update
    sudo apt-get install -y git curl bubblewrap zstd python3 rsync tmux
    python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))' \
      || { echo "python3 must be 3.11 or newer" >&2; exit 1; }
    limits
    command -v elan >/dev/null \
      || curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
    mkdir -p "$JUDGE"

    # 1. The challenge, before anything of the proof has been downloaded as compiled files.
    lake build RH.Challenge
    lake env leanexport RH.Challenge -- $(targets $ALL) > "$JUDGE/challenge.export"

    # 2. Mathlib's compiled files. The name is qualified because the package of the proof
    #    has a `cache` executable of its own.
    lake exe mathlib/cache get

    # 3. The compiled files of the proof. Its cache tool runs from its own root, which is
    #    given this project's packages rather than a second copy of them.
    mkdir -p .lake/packages/tree/.lake
    ln -sfn "$ROOT/.lake/packages" .lake/packages/tree/.lake/packages
    (cd .lake/packages/tree && lake exe cache get)

    # 4. Nothing of the proof may need compiling; then compile this project.
    lake build --no-build tree/Main > "$JUDGE/proof-up-to-date.log" 2>&1 \
      || { echo "the proof is not up to date: see $JUDGE/proof-up-to-date.log" >&2; exit 1; }
    lake build RH Assembly > "$JUDGE/build.log" 2>&1 \
      || { echo "build failed: see $JUDGE/build.log" >&2; exit 1; }
    echo "setup done"
    ;;
  companions)
    limits
    lake env leanexport RH.Solution -- $(targets $COMPANIONS) > "$JUDGE/companions.export"
    # The challenge export of `setup` also names RH.riemann_hypothesis; this one does not.
    lake env leanexport RH.Challenge -- $(targets $COMPANIONS) > "$JUDGE/challenge-companions.export"
    mkdir -p "$JUDGE/run"
    cp "$ROOT/lean-toolchain" "$ROOT/comparator-companions.json" "$JUDGE/run/"
    cd "$JUDGE/run"
    lake comparator --paranoid --config comparator-companions.json \
      --challenge-from-export "$JUDGE/challenge-companions.export" \
      --solution-from-export "$JUDGE/companions.export" 2>&1 | tee "$JUDGE/companions.log"
    ;;
  full)
    limits
    [ -s "$JUDGE/solution.export" ] \
      || lake env leanexport Assembly -- $(targets $ALL) > "$JUDGE/solution.export"
    judge comparator.json "$JUDGE/solution.export" full
    ;;
  *)
    echo "usage: scripts/comparator.sh setup | companions | full" >&2
    exit 2
    ;;
esac
