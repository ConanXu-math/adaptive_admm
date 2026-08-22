# Adaptive ADMM Formalization v2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Publish a local review branch whose default surface is the current, placeholder-free Adaptive ADMM Lean formalization with reproducible examples and CI.

**Architecture:** Treat the Lean proof subtree and its `Strategies.lean` facade as the trusted core. Keep historical search/generation source isolated as legacy, remove generated runtime artifacts from the release surface, and make CI enforce exactly the claims stated in the README.

**Tech Stack:** Lean 4.24.0-rc1, Lake, Mathlib, GitHub Actions, shell-based repository hygiene checks

**Spec:** `doc/FORMALIZATION_SCOPE.md`

## Global Constraints

- Work only on `codex/formalization-v2` in `/private/tmp/adaptive-admm-formalization-v2`.
- Do not push, merge, or modify the user's original dirty worktree.
- Preserve the locked `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`.
- Active formalization and examples must contain no `sorry`, `admit`, or new `axiom` declarations.
- Claims must distinguish checked Lean theorems, concrete examples, historical experiments, and future work.
- Build the default Optlib target, the Adaptive ADMM strategy facade, and the C2 theorem as separate targets because the legacy standard ADMM and Adaptive ADMM modules share top-level declaration names.
- Removed files remain recoverable from Git commit `12c0e5481aa77fbb548f567bb55e563a6e11e823`.

---

### Task 1: Replace the Adaptive ADMM proof core

**Files:**
- Replace: `Optlib/Algorithm/AdaptiveADMM/**`
- Source: `/Users/conanxu/alpha_evolve/lean_workspace/Optlib/Algorithm/AdaptiveADMM/**`

**Interfaces:**
- Consumes: the unchanged project toolchain and the existing `Optlib` dependencies.
- Produces: `Optlib.Algorithm.AdaptiveADMM.Strategies` as the public facade, including `StrategyPolicy`, `CertifiedTau`, template lemmas, and convergence theorem entrypoints.

- [x] **Step 1: Confirm dependency identity**

Run:

```bash
shasum lean-toolchain lakefile.lean lake-manifest.json
shasum /Users/conanxu/alpha_evolve/lean_workspace/lean-toolchain /Users/conanxu/alpha_evolve/lean_workspace/lakefile.lean /Users/conanxu/alpha_evolve/lean_workspace/lake-manifest.json
```

Expected: each corresponding pair has the same SHA-1 digest.

- [x] **Step 2: Synchronize the proof subtree exactly**

Run:

```bash
rsync -a --delete --exclude=.DS_Store /Users/conanxu/alpha_evolve/lean_workspace/Optlib/Algorithm/AdaptiveADMM/ Optlib/Algorithm/AdaptiveADMM/
```

Expected: the target contains 14 Lean files, including `AdaptiveProductBounds.lean`, `Strategies.lean`, and `Strategies/StrategyPolicy.lean`.

- [x] **Step 3: Verify the core before committing**

Run:

```bash
lake build Optlib.Algorithm.AdaptiveADMM.Strategies
lake build Optlib.Algorithm.AdaptiveADMM.AdaptiveTheorem_converge_c2
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false Optlib/Algorithm/AdaptiveADMM/Strategies.lean
lake build
```

Expected: all commands exit 0; each Lake command reports a successful build.

- [x] **Step 4: Commit the proof-core replacement**

```bash
git add Optlib/Algorithm/AdaptiveADMM
git commit -m "feat: publish adaptive ADMM formalization v2"
```

Expected: a local commit on `codex/formalization-v2`; no push occurs.

### Task 2: Narrow the public release surface and add checked examples

**Files:**
- Delete: `lean_admm/alpha_evolve/openevolve_output/**`
- Delete: `res/**`
- Delete: tracked `**/__pycache__/**`, `lean_admm/.idea/**`, and `lean_admm/alpha_evolve/openevolve_output.zip`
- Delete: `sample1/**`, `sample2/**`, `sample3/**`
- Create: `examples/README.md`
- Create: `examples/01_standard_pseries_sum2/**`
- Create: `examples/02_local_atom_sum/**`
- Create: `examples/03_factored_atom_sum/**`
- Modify: `.gitignore`

**Interfaces:**
- Consumes: the stable `Optlib.Algorithm.AdaptiveADMM.Strategies` facade.
- Produces: three independently compilable `certificate.lean` examples and a release tree without runtime artifacts or placeholder examples.

- [x] **Step 1: Record the failing hygiene baseline**

Run:

```bash
grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' sample1 sample2 sample3 --include='*.lean'
```

Expected: matches in the old sample tree, proving it cannot be part of the v2 checked examples.

- [x] **Step 2: Remove only the enumerated generated and stale paths**

Run `git rm -r` on the paths listed under **Files**, after confirming them with `git ls-files`. Do not remove the historical source files under `lean_admm/alpha_evolve/` that are outside `openevolve_output`.

Expected: checkpoints, logs, caches, IDE metadata, and the three old sample directories are staged for deletion; historical source remains.

- [x] **Step 3: Copy the checked example corpus**

Run:

```bash
rsync -a --exclude=.DS_Store /Users/conanxu/alpha_evolve/fewshot_proofs/examples/ examples/
```

Expected: three numbered example directories, each with a `certificate.lean` importing the public facade.

- [x] **Step 4: Extend `.gitignore` with exact runtime-artifact rules**

Add rules for `__pycache__/`, `.idea/`, `openevolve_output/`, `res/openevolve_output/`, and generated Adaptive ADMM proof drafts. Do not ignore source `.lean`, `.py`, `.json`, or `.md` files generally.

- [x] **Step 5: Compile every new certificate**

Run:

```bash
find examples -name certificate.lean -print0 | xargs -0 -n1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
```

Expected: all three files exit 0.

### Task 3: Document claims and enforce them in CI

**Files:**
- Replace: `README.md`
- Create: `doc/FORMALIZATION_SCOPE.md`
- Create: `.github/workflows/lean.yml`

**Interfaces:**
- Consumes: the Lean facade, three certificates, and the scope contract.
- Produces: a reader-facing claim ledger and CI gates matching the local verification commands.

- [x] **Step 1: Rewrite the README around the checked core**

Document the theorem surface, non-claims, module map, examples, exact local commands, repository boundary, and the status of the legacy generator. Remove success-rate estimates and any suggestion that `sorry` is an accepted fallback.

- [x] **Step 2: Add GitHub Actions validation**

Use `actions/checkout@v4` and `leanprover/lean-action@v1`. Run the project build, strict facade compilation, all example certificates, and a placeholder scan limited to `Optlib/Algorithm/AdaptiveADMM` plus `examples`.

- [x] **Step 3: Run the same checks locally**

Run:

```bash
lake build
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false Optlib/Algorithm/AdaptiveADMM/Strategies.lean
find examples -name certificate.lean -print0 | xargs -0 -n1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
! grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' Optlib/Algorithm/AdaptiveADMM examples --include='*.lean'
```

Expected: every command succeeds and the final scan prints no matches.

- [x] **Step 4: Commit release documentation, examples, and CI**

```bash
git add README.md .gitignore .github examples doc docs lean_admm res sample1 sample2 sample3
git commit -m "docs: define the formalization v2 release surface"
```

Expected: a second local commit; no push occurs.

### Task 4: Final repository audit

**Files:**
- Inspect: all changes from `origin/main..codex/formalization-v2`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: evidence that the local review branch is buildable, scoped, and free of accidental generated files.

- [x] **Step 1: Verify source synchronization**

Run:

```bash
diff -qr --exclude=.DS_Store /Users/conanxu/alpha_evolve/lean_workspace/Optlib/Algorithm/AdaptiveADMM Optlib/Algorithm/AdaptiveADMM
```

Expected: no output.

- [x] **Step 2: Verify tracked-file hygiene and patch integrity**

Run:

```bash
git diff origin/main...HEAD --check
git ls-files | grep -E '(^|/)(__pycache__|\.idea)(/|$)|(^|/)openevolve_output(/|$)|^res/'
```

Expected: `git diff --check` exits 0 and the tracked-file query prints no matches.

- [x] **Step 3: Repeat the full proof gate from a clean status**

Run the four commands from Task 3 Step 3, then run `git status --short --branch`.

Expected: all proof gates succeed and the branch has no uncommitted changes.

- [x] **Step 4: Prepare the review handoff**

Record the branch name, worktree path, commit IDs, changed-file summary, deletion scope, proof commands, and the fact that nothing was pushed.
