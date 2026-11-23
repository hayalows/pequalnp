#!/usr/bin/env bash
# Run only inside an OpenAI-managed Codex Cloud environment.
set -euo pipefail
fail() { printf 'Lean cloud setup: %s\n' "$*" >&2; exit 1; }
[[ "${PEQUALNP_CLOUD_CONFIRMED:-}" == 1 ]] || fail 'Run only in Codex Cloud; set PEQUALNP_CLOUD_CONFIRMED=1 to attest this.'
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_dir/lean-cloud-env.sh"
repo_dir="$(cd -- "$script_dir/.." && pwd -P)"
proofs="${PEQUALNP_PROOFS_DIR:-}"
if [[ -z "$proofs" ]]; then
  if [[ -f "$repo_dir/../pequalnp-proofs/lean/lean-toolchain" ]]; then
    proofs="$repo_dir/../pequalnp-proofs"
  elif [[ -f "$repo_dir/proofs/lean/lean-toolchain" ]]; then
    proofs="$repo_dir/proofs"
  else
    fail 'Proofs checkout missing; select both repositories or set PEQUALNP_PROOFS_DIR.'
  fi
fi
for cmd in git curl python3 sha256sum tar awk grep; do
  command -v "$cmd" >/dev/null || fail "Missing required tool: $cmd"
done
[[ -f "$proofs/lean/lean-toolchain" && -f "$proofs/lean/lake-manifest.json" && -f "$proofs/lean/lakefile.toml" ]] || fail "Not a Lean proofs checkout: $proofs"
origin="$(git -C "$proofs" remote get-url origin)" || fail 'Could not read proofs origin.'
case "$origin" in
  https://github.com/hayalows/pequalnp-proofs|https://github.com/hayalows/pequalnp-proofs.git|git@github.com:hayalows/pequalnp-proofs.git) ;;
  *) fail "Unexpected proofs origin: $origin" ;;
esac
cd "$proofs/lean"
[[ "$(cat lean-toolchain)" == 'leanprover/lean4:v4.36.0' ]] || fail 'Unexpected Lean toolchain; expected leanprover/lean4:v4.36.0.'
python3 - <<'PY'
import json, sys
with open('lake-manifest.json', encoding='utf-8') as f: manifest = json.load(f)
m = [p for p in manifest['packages'] if p['name'] == 'mathlib']
if len(m) != 1 or m[0]['rev'] != 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842':
    sys.exit('Lean cloud setup: unexpected Mathlib revision.')
PY
# Exact bytes from the reviewed proofs commit 7b050d788a8bcad6f2ed5e53cdb2e26bd6109257.
echo 'd0af863cde532caaef1b1bee0d63ec47100208e33e488309cb80abc88b8f1509  lake-manifest.json' | sha256sum -c - || fail 'Lockfile differs from reviewed baseline.'
echo 'ee756ab61cf24d2fd5f561d89080cf162e34f35b06d9b6101bc680ef1619a7bf  lakefile.toml' | sha256sum -c - || fail 'Lake configuration differs from reviewed baseline.'
[[ -z "$(git status --porcelain --untracked-files=no -- lean-toolchain lake-manifest.json lakefile.toml)" ]] || fail 'Lean configuration has tracked modifications.'
# Reject modified, replaced, or differently pinned dependency checkouts; never reset them.
python3 - <<'PY'
import json, os, subprocess, sys
with open('lake-manifest.json', encoding='utf-8') as f: manifest = json.load(f)
def git(path, *args):
    return subprocess.run(['git', '-C', path, *args], capture_output=True, text=True, check=True).stdout.strip()
for p in manifest['packages']:
    path = os.path.abspath(os.path.join(manifest.get('packagesDir', '.lake/packages'), p['name']))
    if not os.path.lexists(path): continue
    try:
        root = os.path.realpath(git(path, 'rev-parse', '--show-toplevel'))
        rev = git(path, 'rev-parse', 'HEAD')
        dirty = git(path, 'status', '--porcelain', '--untracked-files=normal')
        url = git(path, 'remote', 'get-url', 'origin').removesuffix('.git')
        if root != os.path.realpath(path) or rev != p['rev'] or dirty or url != p['url'].removesuffix('.git'):
            raise ValueError('root, revision, origin, or working tree differs')
    except (OSError, subprocess.CalledProcessError, ValueError) as e:
        sys.exit(f'Lean cloud setup: refusing to alter dependency {path}: {e}')
PY
mkdir -p "$ELAN_HOME" "$XDG_CACHE_HOME/mathlib"
tmp="$(mktemp -d "$XDG_CACHE_HOME/lean-setup.XXXXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  [[ "$(uname -sm)" == 'Linux x86_64' ]] || fail 'Elan bootstrap supports Linux x86_64 only.'
  curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
    https://github.com/leanprover/elan/releases/download/v4.4.0/elan-x86_64-unknown-linux-gnu.tar.gz -o "$tmp/elan.tar.gz"
  echo '0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2  '"$tmp/elan.tar.gz" | sha256sum -c - || fail 'Elan archive checksum mismatch.'
  tar -xzf "$tmp/elan.tar.gz" -C "$tmp" elan-init
  "$tmp/elan-init" -y --no-modify-path --default-toolchain none
fi
for tool in elan lean lake; do
  [[ "$(command -v "$tool")" == "$ELAN_HOME/bin/$tool" ]] || fail "Unexpected $tool on PATH."
  echo '54238e7fc23ede3da0d3705830b1c81c86d1e6e3e4886395e2f9f16375ad0d9b  '"$ELAN_HOME/bin/$tool" | sha256sum -c - || fail "Unexpected $tool launcher; expected official Elan 4.4.0."
done
[[ "$(elan --version)" == 'elan 4.4.0 ('* ]] || fail 'Unexpected Elan version.'
if ! elan toolchain list | awk '{print $1}' | grep -Fx 'leanprover/lean4:v4.36.0' >/dev/null; then
  elan toolchain install leanprover/lean4:v4.36.0
else
  echo 'Pinned Lean toolchain already installed.'
fi
[[ "$(lean --version)" == 'Lean (version 4.36.0,'* ]] || fail 'Installed Lean version does not match the pin.'
# Limit Lake/Lean task parallelism on the observed 2-CPU, 8-GiB machine.
export LEAN_NUM_THREADS=1 MATHLIB_CACHE_PARALLEL_MAX=8
export MATHLIB_CACHE_DIR="$XDG_CACHE_HOME/mathlib"
[[ -z "${MATHLIB_CACHE_GET_URL:-}" ]] || fail 'Custom Mathlib cache URL is not allowed.'
lake exe cache get 2>&1 | tee "$tmp/cache.log" || fail 'Mathlib cache retrieval failed.'
if grep -Eq 'not in the cache|still missing after all scopes' "$tmp/cache.log"; then
  fail 'Mathlib cache is incomplete.'
fi
[[ -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]] || fail 'Mathlib root artifact is missing.'
cat > "$tmp/CloudSmoke.lean" <<'LEAN'
import Mathlib

theorem cloud_setup_smoke (n : ℕ) : n + 0 = n := by simp
LEAN
lake env lean "$tmp/CloudSmoke.lean" || fail 'Mathlib smoke theorem failed.'
lake build Mathlib PEqualNP checklemma || fail 'Required project build failed.'
printf 'Lean cloud setup and validation succeeded in %s\n' "$PWD"
