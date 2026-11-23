# Lean setup in Codex Cloud

Use only in an OpenAI-managed Codex Cloud environment. Select both `hayalows/pequalnp` and `hayalows/pequalnp-proofs`. The script recognizes a sibling `pequalnp-proofs`, a `proofs/` checkout inside this repository, or `PEQUALNP_PROOFS_DIR`. It checks the origin and never resets the fork or updates the lockfile. Lake writes ignored dependencies and build outputs under the fork's `lean/.lake`.

## Install command

After these files are committed and available in the cloud checkout, configure:

```bash
PEQUALNP_CLOUD_CONFIRMED=1 bash /workspace/pequalnp/scripts/lean-cloud-setup.sh
```

`PEQUALNP_CLOUD_CONFIRMED=1` is an explicit attestation by the person configuring the environment, not technical proof of cloud execution. The availability of `CODEX_CI` and `CODEX_ENVIRONMENT_ID` during Install is undocumented, so the script does not depend on them. Verify the environment is OpenAI-managed before setting the attestation. If the workspace checkout has a different path, adjust the command accordingly.

The script requires Bash, Git, curl, Python 3, sha256sum, tar, awk, grep and a Linux x86_64 host for Elan bootstrap. It checks the complete lockfile and Lake configuration against SHA-256 digests from previously verified proofs commit `7b050d788a8bcad6f2ed5e53cdb2e26bd6109257`, explicitly checks Lean 4.36.0 and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and refuses changed dependency checkouts. Updating these pins requires a separate reviewed change. It checks the Elan 4.4.0 launcher binaries against the digest of the official release executable; a missing Elan is downloaded from the official release and verified against the pinned archive digest.

Lake retrieves missing locked checkouts and the Mathlib cache; the script rejects reported missing cache files, compiles a temporary theorem importing Mathlib, and runs `lake build Mathlib PEqualNP checklemma`. It sets `LEAN_NUM_THREADS=1` and limits cache transfers to eight. The cache download uses the official endpoint. Existing `ELAN_HOME` and `XDG_CACHE_HOME` override `/workspace/.elan` and `/workspace/.cache`; Mathlib's cache is placed in `$XDG_CACHE_HOME/mathlib`. The tested setup occupied about 12 GiB. Permit GitHub release/dependency hosts and `cache.mathlib.org` in the network policy.

## Start configuration

Configure task environment variables when supported:

```text
ELAN_HOME=/workspace/.elan
XDG_CACHE_HOME=/workspace/.cache
```

Prepend `/workspace/.elan/bin` to the existing PATH. Alternatively source the helper in every shell that invokes Lean or Lake:

```bash
source /workspace/pequalnp/scripts/lean-cloud-env.sh
```

For a Start skill instruction field, use:

```text
Before running Lean or Lake, source /workspace/pequalnp/scripts/lean-cloud-env.sh in the same shell command. Use the existing hayalows/pequalnp-proofs checkout and its pinned lean/lean-toolchain and lake-manifest.json. Do not update dependencies or claim a research assignment as part of startup.
```

A standalone startup process cannot export variables to other shell processes. A published snapshot must include `/workspace/.elan`, `/workspace/.cache`, and the proofs checkout's ignored `.lake` directory to avoid downloads. Verify that in a new task; otherwise Install reconstructs the setup from the pins. A full installation in a completely empty fresh environment has not yet been tested. The cloud configuration's Install/Start field availability and snapshot contents must be checked in its Edit flow.
