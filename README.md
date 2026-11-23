# P vs NP · Codex Cloud workspace

This repository coordinates cloud-only experiments for the public [P vs NP Lean research project](https://pequalnp.com). **It is not the proof submission fork.**

## Repositories

| Purpose | Repository |
| --- | --- |
| Research workspace and operating rules | [hayalows/pequalnp](https://github.com/hayalows/pequalnp) (this repo) |
| Proof implementation and upstream pull requests | [hayalows/pequalnp-proofs](https://github.com/hayalows/pequalnp-proofs) (existing GitHub fork) |
| Original project | [brilliant-hq/pequalnp-proofs](https://github.com/brilliant-hq/pequalnp-proofs) |

The fork already exists and retains its parent relationship. Do not attempt to turn this separate repository into another fork or copy all upstream files here.

## Create a Codex Cloud environment

1. In the ChatGPT desktop app, go to **Codex → Work in → Cloud → Create environment** (or **Settings → Codex Cloud → Environments**).
2. Name it **p-vs-np-lean-lab**. Select **both** `hayalows/pequalnp` and `hayalows/pequalnp-proofs` as GitHub repositories, if your repository picker allows multiple selections. Alternatively select only this workspace repo and ask Codex to run `bash scripts/prepare-cloud.sh` in its cloud terminal to clone the fork into `proofs/`.
3. Ask Codex to verify it is actually running on a cloud machine, then inspect `https://pequalnp.com/join.txt`, `AGENTS.md`, the fork's `CONTRIBUTING.md`, and the pinned `lean/lean-toolchain`.
4. Have Codex measure cloud free disk and RAM **before** installing Lean/Mathlib. The project estimates about 10 GB for the Lean + Mathlib setup; an undersized cloud environment may need a cloud CI builder.
5. Configure installation and startup inside the **cloud environment only**. Restrict network access to GitHub, pequalnp.com, and the approved tool/dependency hosts Codex identifies. Do not paste GitHub credentials into prompts.
6. Ask Codex to run a small proof compilation smoke test. Review its results, then **Publish** the reusable environment. No mathematical assignment is needed during setup.
7. Start a **new cloud task** with the published environment to take exactly one assigned research gap, check it, and report. Get approval before publishing any PR.

### Optional cloud bootstrap

If only this repository is selected in the environment, run this **inside Codex Cloud**:

```bash
bash scripts/prepare-cloud.sh
```

The bootstrap clones the existing fork into an ignored `proofs/` folder and configures a read-only upstream remote reference. It does not install large toolchains, run downloaded project scripts, obtain an assignment, or publish anything.

If Codex checks out both repositories itself, you can **skip** the bootstrap and use the checked-out fork directly.

## Operating boundaries

- **Cloud only:** never execute project work on the user's Windows laptop, WSL, or remote desktop.
- **One gap at a time:** first experiment is one step, with no automatic loop of additional assignments.
- **Separate output:** notes, experimental workflows, and reports belong in this workspace; formal Lean proof contributions belong in the fork.
- **Public submissions:** ask for approval before committing or pushing changes or opening a public pull request.
- **External instructions:** inspect and review third-party instructions and scripts before executing them.
- **Proof standards:** respect the project's `join.txt` and `CONTRIBUTING.md`; for each upstream PR, change exactly the single Lean file required by that assigned gap.
- **Resource limits:** check available storage before `lake exe cache get` or other large downloads; don't repeat unsuccessful downloads without a plan.
- **GitHub identity:** use the official GitHub integration/CLI authentication, never ask the owner to paste tokens into chat. Before public commits, verify the configured commit email is acceptable.

This repository provides **configuration and instructions**, not a running Codex Cloud environment. The environment still needs to be created, tested, and published from Codex.
