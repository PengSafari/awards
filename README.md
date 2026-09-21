# awards — PengSafari's mathematical formalizations

One maintained home for three complete Lean formalization projects and our Justin Sun Prize submissions. This is **PengSafari's personal fork**, not the prize organizer's official repository. The upstream catalog remains available here for contributing through isolated submission branches.

## Proof projects

| Project | Complete formalized result | Upstream submission |
|---|---|---|
| [JSP-000391](proofs/jsp-000391/README.md) | Stoll's arbitrary-base digit recurrence, all positive real targets and admissible shifts, with reconstruction convergence | [PR #1163](https://github.com/TheJustinSunPrize/awards/pull/1163) |
| [JSP-000690](proofs/jsp-000690/README.md) | Li's chromatic-critical 3-uniform hypergraph, with 9 vertices, 22 edges and minimum degree 7 | [PR #1152](https://github.com/TheJustinSunPrize/awards/pull/1152) |
| [JSP-000746](proofs/jsp-000746/README.md) | Independent Schur triples in triangle-free integer graphs, with exact finite threshold 18 | [PR #1164](https://github.com/TheJustinSunPrize/awards/pull/1164) |

These formalize known mathematical results. Each project retains its own precise statement, mathematical attribution, AI assistance disclosure, MIT license, pinned dependencies and verification evidence. Contribution roles and limitations are described in each `NOTICE.md`.

```text
awards/
├── proofs/
│   ├── jsp-000391/
│   ├── jsp-000690/
│   ├── jsp-000746/
│   └── manifest.json
├── .github/workflows/verify-proofs.yml
└── ... upstream prize catalog and contribution tooling
```

## Build and verify

Each proof remains an independent Lake project using Lean 4.30.0 and a fixed Mathlib revision. Choose one project and follow its README, for example:

```sh
cd proofs/jsp-000391
lake exe cache get Mathlib.Analysis.SpecialFunctions.Log.Base Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
python3 verify.py --clean
```

For JSP-000690, the verifier is `python3 scripts/verify.py --clean`; for the other two it is `python3 verify.py --clean`. The [matrix workflow](.github/workflows/verify-proofs.yml) runs the three projects independently, including their axiom audits and fresh Lean kernel replay. A configured workflow is not itself a passed result; inspect the run and its receipt for the chosen commit.

## Migration and submissions

The original standalone repositories have been consolidated with their full Git histories. All submitted source commit identities remain reachable from this repository's `main` branch. The current working copies are under `proofs/`; older pinned commits retain their original root layout. See [migration and provenance](docs/proof-consolidation.md) and the [source identity manifest](proofs/manifest.json).

The original repositories are retained as read-only historical archives so existing commit and GitHub Actions links continue to work. Future proof development belongs here. The three catalog submission branches remain separate from this monorepo's main branch so no proof source is included in the upstream catalog PRs.

## Upstream catalog and licenses

The [original upstream README](UPSTREAM-README.md), [problem bank](problems/README.md), [contribution rules](CONTRIBUTING.md) and [record tools](docs/records.md) are preserved. The official repository is [TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards).

Each proof project's code and documentation retains its own MIT license. Upstream code and records retain [LICENSE](LICENSE) and [LICENSE-CONTENT](LICENSE-CONTENT). No prize acceptance or award entitlement is asserted by this repository.
