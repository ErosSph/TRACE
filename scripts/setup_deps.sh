#!/usr/bin/env bash
# Check out the pinned Coq dependencies (git submodules under dep/), apply the small Coq 8.18
# compatibility patches, and install FreeSim into the active opam switch.  Run from the repository root.
set -euo pipefail
cd "$(dirname "$0")/.."
git submodule update --init dep/coqutil dep/riscv-coq dep/VerilRocq   # not recursive: only FreeSim is used from VerilRocq
apply() {  # dir patch
  if git -C "$1" apply --check "$2" 2>/dev/null; then git -C "$1" apply "$2"; echo "patched $1"
  elif git -C "$1" apply --check --reverse "$2" 2>/dev/null; then echo "$1 already patched"
  else echo "cannot apply $2 to $1" >&2; exit 1; fi
}
apply dep/coqutil   "$PWD/dep-patches/coqutil.patch"
apply dep/riscv-coq "$PWD/dep-patches/riscv-coq.patch"
opam install -y ./dep/VerilRocq/dep/FreeSim   # coq-freesim (Stuttering for Free, OOPSLA'23), BSD-3-Clause
echo "dependencies ready"
