#!/usr/bin/env bash
# Cloud-only helper: fetch the already-existing GitHub fork without installing or running it.
set -euo pipefail

if [[ -z "${BASH_VERSION:-}" ]]; then
  echo "This helper requires Bash." >&2
  exit 1
fi
if ! command -v git >/dev/null 2>&1; then
  echo "git is not installed in this environment." >&2
  exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."
fork="https://github.com/hayalows/pequalnp-proofs.git"
upstream="https://github.com/brilliant-hq/pequalnp-proofs.git"
target="proofs"

if [[ -e "$target" && ! -d "$target/.git" ]]; then
  echo "Refusing: '$target' exists but is not a Git checkout." >&2
  exit 1
fi
if [[ ! -d "$target/.git" ]]; then
  echo "Cloning the user's EXISTING fork inside this cloud workspace..."
  git clone --filter=blob:none "$fork" "$target"
fi

origin="$(git -C "$target" remote get-url origin)"
case "$origin" in
  "$fork"|"https://github.com/hayalows/pequalnp-proofs"|"git@github.com:hayalows/pequalnp-proofs.git") ;;
  *) echo "Refusing: '$target' origin is not the expected fork: $origin" >&2; exit 1 ;;
esac

if ! git -C "$target" remote get-url upstream >/dev/null 2>&1; then
  git -C "$target" remote add upstream "$upstream"
fi

if [[ ! -f "$target/lean/lean-toolchain" || ! -f "$target/CONTRIBUTING.md" ]]; then
  echo "The checkout does not contain the expected Lean project files." >&2
  exit 1
fi

echo "Fork checkout ready at: $PWD/$target"
echo "Pinned Lean toolchain: $(cat "$target/lean/lean-toolchain")"
echo "Next: inspect CONTRIBUTING.md and join.txt, check disk, install the toolchain in Codex Cloud."
echo "No toolchain installed; no proof assignment claimed; no GitHub changes pushed."
