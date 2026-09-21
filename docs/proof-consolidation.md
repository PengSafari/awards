# Proof repository consolidation

On 2026-09-21, PengSafari requested one maintained `awards` repository for the upstream fork and the three proof projects. The personal fork now hosts the projects under `proofs/`.

## Identity and history

The standalone histories were imported with `git subtree add` **without squash**. Their original commits are ancestors of the consolidated `main`; this is not a rewrite of a submitted proof. Every Lean file is copied byte-for-byte. The [manifest](../proofs/manifest.json) records each source repository, selected commit, original tree, PR, original successful CI run, and Lean source hashes.

A URL using an original selected commit still addresses that commit's **original root layout**, such as `blob/<original-commit>/Jsp391/Main.lean`. Current development uses `tree/main/proofs/jsp-000391`. To reproduce an original submission, check out its selected commit first; to work on the current monorepo, change into the corresponding `proofs/` directory.

Existing `verification/local` files are immutable historical records of their source versions. Their checkout commit, relative paths and hashes refer to those versions, before this README migration. New matrix runs write new receipts under each project's ignored `verification/current/` and identify the consolidated checkout commit.

## Build isolation

Each directory retains its own Lake configuration and dependency pins. No Lean theorem, certificate, SAT instance or mathematical assumption was changed for the move. Workflows inside the subdirectories are preserved historical files; GitHub executes the root `.github/workflows/verify-proofs.yml` matrix for ongoing verification.

The original standalone repositories are retained read-only after a migration notice. Their original commit URLs and Actions evidence remain available. Historical Actions artifacts still have their original retention periods; important receipts have also been saved in the local project records.

## Upstream pull requests

The organizer accepts proof references in its catalog, not proof source files. Accordingly the three `codex/jsp-000…-formalization` branches remain based on the upstream catalog. Migration updates on those branches only change proof-host references, while keeping the originally submitted source commit identities and mathematical scope. The monorepo main branch must not be merged into those catalog branches.

PengSafari remains the repository owner and project director. Original mathematical authors and all earlier formalization disclosures remain in each project's NOTICE. Consolidation makes no new priority, authorship, independent-review or award claim.
