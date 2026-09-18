# JSP-000746: independent Schur triples in triangle-free graphs

This repository gives a complete Lean 4 proof of the integer-graph assertion in **JSP-000746 / [Erdős problem 895](https://www.erdosproblems.com/895)**, including the exact finite threshold **18** and an explicit obstruction on 17 vertices. The original affirmative answer and the upper bound of 18 remain credited to **Ben Barber**, as recorded on the problem page.

This is a human-directed, AI-assisted formalization project. **PengSafari** directed the project and authorized submission; **OpenAI Codex** generated the implementation, certificates, and verification tooling and performed the recorded checks. See [NOTICE.md](NOTICE.md) for provenance and prior work. No mathematical discovery, first-formalization priority, edge-minimality, or award entitlement is claimed.

## Full statement

`Jsp746.integer_graph`, in [Jsp746/Main.lean](Jsp746/Main.lean), proves that every triangle-free simple graph on **all integers** contains integers

\[
0<a<b<a+b\le18
\]

such that `a`, `b`, and `a+b` are pairwise nonadjacent. The graph is an ordinary Mathlib `SimpleGraph ℤ`, triangle-freeness is `CliqueFree 3`, and addition is ordinary integer addition. There is no finiteness assumption, no zero or repeated summand, and no certificate hypothesis in this theorem. `Jsp746.natural_graph` gives the corresponding natural-number theorem.

For each natural number `n`, label the vertices `i : Fin n` by the positive integers `i.val + 1`. The predicate `FiniteSchurProperty n` says that every triangle-free graph on these labels contains two distinct positive summands and their sum as three pairwise nonadjacent vertices. The theorem

```lean
Jsp746.finite_threshold (n : ℕ) : FiniteSchurProperty n ↔ 18 ≤ n
```

proves the exact threshold for **all** natural numbers, including empty and small intervals. `Jsp746.seventeen_counterexample` supplies the lower-bound graph, and `Jsp746.witness_edge_count` proves that this particular graph has exactly **42 unordered edges**. Its edge count is not asserted to be optimal. The stronger Hindman-set question mentioned separately in the problem record is outside the theorem proved here.

## Proof and statement correspondence

| Mathematical step | Source |
| --- | --- |
| Explicit triangle condition is equivalent to Mathlib `CliqueFree 3`; finite positive-label convention | [Graph.lean](Jsp746/Graph.lean) |
| Independently searched 17-vertex obstruction, its triangle-freeness, Schur-triple coverage, and 42-edge count | [Witness.lean](Jsp746/Witness.lean) |
| Initial clauses follow from the precise triangle and Schur hypotheses | [Certificate/Initial.lean](Jsp746/Certificate/Initial.lean) |
| Ordinary propositional derivations of learned clauses | [Certificate/](Jsp746/Certificate/) |
| Contradiction if every eligible triple on 18 labels contains an edge | [Refutation.lean](Jsp746/Refutation.lean) |
| Integer/natural graph interfaces and exact threshold for all finite intervals | [Main.lean](Jsp746/Main.lean) |
| Ten named theorem axiom closures | [Audit.lean](Audit.lean) |

The upper-bound SAT instance has 153 edge variables and 888 clauses: 816 exclude triangles and 72 exclude independent Schur triples with distinct positive summands. Our own search trace has 2,123 learned-clause additions. Dependency pruning retains 840 initial and 1,821 learned clauses; their Lean proofs explicitly replay 57,385 unit propagations across 31 proof chunks.

The upper bound first gives a triple in the first 18 positive labels. Restriction transfers it to arbitrary integer graphs and to every larger interval. Restricting the 17-vertex obstruction proves failure on every smaller interval. The lower-bound finite facts use `decide +kernel`, not native evaluation.

## Reproduce

Install [elan](https://github.com/leanprover/elan), Python 3.9 or later, and Git. `lean-toolchain` selects **Lean 4.30.0**. Mathlib is pinned to **c5ea00351c28e24afc9f0f84379aa41082b1188f**; the checked-in manifest pins every transitive dependency.

From this repository's directory:

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Clique Mathlib.Tactic.Tauto Mathlib.Tactic.NormNum
python3 verify.py --clean
```

The script deletes only this project's compiled output, preserves dependency caches, rebuilds with warnings treated as failures, audits exactly ten named theorem closures, and replays the entire imported environment with `leanchecker --fresh`. It also checks the packaged CNF encodings and 42-edge witness in Python. It rejects missing audit results, unexpected axioms, forbidden proof-source constructs, or any failed command. Logs and source hashes are written to `verification/current/receipt.json` and adjacent logs.

The [GitHub Actions workflow](.github/workflows/verify.yml) performs these checks on Ubuntu and preserves logs as an artifact. [Committed local evidence](verification/local/) records checks on the submitter's machine. These are contributor-produced verification records, not organizer approval or independent human review.

**No SAT solver is required to build or verify the Lean proof.** The checked-in Lean sources contain explicit theorem bodies, rather than a call to a solver or Python oracle. The SAT solver, RUP checker, and source generator are untrusted discovery tools: Lean checks their output as ordinary proof terms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in the ten audited axiom closures. The official fresh replay uses Lean's own kernel, not a second independently implemented type checker.

## Certificate regeneration

The repository includes the original CNFs, 18-vertex trace, and 42-edge witness data under [data/](data/). To reproduce the translation from the saved trace without rerunning a solver:

```sh
python3 scripts/check_rup.py
python3 scripts/generate_refutation.py
python3 verify.py --clean
```

See [scripts/README.md](scripts/README.md) for the architecture and optional fresh SAT search. Regeneration is unnecessary for verifying the existing proof; using another solver version may produce a different valid trace or witness.

## Prior work and license

Known related submissions include [PR #165](https://github.com/TheJustinSunPrize/awards/pull/165), [PR #402](https://github.com/TheJustinSunPrize/awards/pull/402), and [PR #738](https://github.com/TheJustinSunPrize/awards/pull/738). Their existence and original contributions are acknowledged; no other submitter's 746 Lean implementation or proof certificate was read, imported, or copied in developing this implementation. This is not a claim that no other relevant work exists.

Original code, scripts, generated proof terms, data, and documentation in this repository are offered under the [MIT license](LICENSE). Mathlib and the toolchain remain separately licensed dependencies. Mathematical attribution is independent of software licensing.
