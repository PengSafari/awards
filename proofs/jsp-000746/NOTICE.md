# Attribution and provenance

- **Mathematics:** Ben Barber is credited with the affirmative answer and the `n ≥ 18` upper bound in the [Erdős problem 895 record](https://www.erdosproblems.com/895). The theorem was known before this project. This repository claims no new mathematical resolution.
- **Project direction and submission authorization:** PengSafari selected and directed the project and authorized publication and submission using their own account. These roles are not represented as independent mathematical or kernel verification.
- **Implementation and verification:** OpenAI Codex generated the Lean implementation, an independent SAT encoding/search trace, the 42-edge witness, the ordinary propositional certificate translation, supporting scripts, and documentation, and performed the recorded checks. This is explicitly AI-assisted work; the submitting account is not credited as the original mathematical solver.
- **Dependencies:** Lean and Mathlib provide the kernel, standard foundations, graph definitions, arithmetic, and tactics. They retain their own attribution and licenses and are not republished as project-authored code.
- **Verification tooling lineage:** The packaging and verification runner follow this contributor's earlier JSP-000690 package, with a new exact ten-theorem audit and the 746-specific data checks. The 746 proof modules were copied byte-for-byte from this project's already checked local development into this standalone package.

## Independent implementation and overlap

The graph encoding and saved SAT trace were generated locally for this project. The 17-point graph is the 42-edge witness produced by that search. The source generator translates the saved 18-point trace into explicit Lean proof terms; it does not copy another proof repository or rely on a checked SAT-solver result as an assumption. The finite witness, the generated propositional proof, and the graph interfaces are original implementations for this project.

Known overlapping public records include [awards PR #165](https://github.com/TheJustinSunPrize/awards/pull/165), [#402](https://github.com/TheJustinSunPrize/awards/pull/402), and [#738](https://github.com/TheJustinSunPrize/awards/pull/738). Those records were consulted to understand prior scope and avoid priority claims. Other submitters' 746 Lean sources and certificates were not read or copied. The list is not an exhaustive literature or submission survey.

The original result, existing formalizations, and any stronger edge-minimality result remain the work of their respective contributors. We claim neither first formalization nor worldwide novelty of the explicit graph. We prove that our graph has 42 edges, not that 42 is a minimum. We do not prove the separate stronger Hindman-set question.

## Evidence boundary

Build receipts, axiom audits, and CI runs are submitter-operated evidence. `leanchecker --fresh` replays the imported declarations with the official Lean kernel; it is not independent kernel software. Python and SAT checks assist discovery and corroboration but are not premises of the final Lean theorems. No organizer-designated reviewer, independent human verification, eligibility decision, or entitlement to an award is asserted.

The MIT license covers this repository's original code, generated proof terms, data, and documentation. It does not relicense cited mathematical sources or external dependencies.
