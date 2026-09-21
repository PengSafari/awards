# JSP-000391: Stoll's arbitrary-base digit recurrence in Lean

This repository formalizes **Theorem 1.3 of Thomas Stoll (2005)** for every integer base, positive real target, and admissible shift. It is a human-directed, AI-assisted formalization project by **PengSafari and OpenAI Codex**. Stoll and the earlier authors retain credit for the mathematics.

[Erdős problem 482](https://www.erdosproblems.com/482), corresponding to JSP-000391, asks for analogues of the Graham–Pollak digit recurrence for square roots and other algebraic numbers. The original question is open-ended. Our precise target is Stoll's all-positive-real, all-base construction, which in particular covers every positive algebraic real. The result is not new mathematics, and [PR 293](https://github.com/TheJustinSunPrize/awards/pull/293) already presents a complete formalization of the same theorem. See [NOTICE.md](NOTICE.md) for roles and prior-source inspection disclosure.

## Complete mathematical statement

Let $g\in\mathbb N$, $g\ge2$, and $w\in\mathbb R$, $w>0$. Set

$$m=\lfloor\log_g w\rfloor\in\mathbb Z,\qquad t=w/g^m,\qquad 1\le t<g,$$

$$a=\frac{g}{(g-1)(t+g)},\qquad b=(g-1)(t+g)=g/a.$$

For **every** real shift

$$-1/g\le\varepsilon<(g+1)(g-2)/g,$$

define the actual integer recurrence by $U_0=1$ and

$$U_{n+1}=\begin{cases}
\lfloor a(U_n+\varepsilon)\rfloor,&n\text{ even},\\
\lfloor b(U_n+1/(g-1))\rfloor,&n\text{ odd}.
\end{cases}$$

For every $n\ge0$, the extracted digit is

$$D_n=U_{2n+2}-gU_{2n}
=\lfloor tg^n\rfloor-g\lfloor tg^n/g\rfloor.$$

We prove $0\le D_n<g$, $D_0\ge1$, and the exact finite reconstruction identity

$$P_n=\sum_{i=0}^{n}D_i/g^i=\lfloor tg^n\rfloor/g^n.$$

Finally, the scaled reconstructions $R_n=g^mP_n$ converge to **the original target $w$**. The digit convention selects the terminating expansion when two radix expansions exist.

The allowed shift interval is nonempty for every permitted base: $\varepsilon=-1/g$ always works. For $g=2$ it is $[-1/2,0)$. The integer normalization exponent handles targets below one as well as exact powers of the base.

**Index correspondence:** our $U_n$ is the paper's $u_{n+1}$; our digit $D_0$ is its first significant digit. The generalized recurrence has $U_1=0$, so it is not described as a strictly positive sequence.

## Source and proof organization

Thomas Stoll, *On Families of Nonlinear Recurrences Related to Digits*, Journal of Integer Sequences 8 (2005), Article 05.3.2. [Primary paper](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf): Theorem 1.3 on page 3, proof on pages 6–7.

| Mathematical assertion | Lean source and declaration |
| --- | --- |
| Actual alternating floor recurrence | [Core.lean](Jsp391/Core.lean), `trajectory` |
| Closed forms for both halves of every pair | [Core.lean](Jsp391/Core.lean), `trajectory_pairs` |
| All-position digit extraction, including the leading digit | [Core.lean](Jsp391/Core.lean), `extraction` |
| Ordinary digits, bounds, finite weighted reconstruction | [Digits.lean](Jsp391/Digits.lean), `digit_bounds`, `digit_zero`, `partialSum_eq` |
| Integer-exponent normalization and reconstruction | [Normalization.lean](Jsp391/Normalization.lean), `normalized_bounds`, `normalized_reconstruct` |
| Full quantified theorem and convergence to $w$ | [Main.lean](Jsp391/Main.lean), **`Jsp391.jsp_000391`** |
| Explicit permitted shift and paper coefficient identity | [Main.lean](Jsp391/Main.lean), `admissible_choice`, `beta_eq_div_alpha` |

The core proof derives the pair identities $U_{2k+1}=\sum_{j<k}g^j$ and $U_{2k+2}=\lfloor(t+g)g^k\rfloor$ from the recursion. Its contracting step clears a positive denominator and uses $\lfloor x\rfloor\le x<\lfloor x\rfloor+1$ together with the shift bounds. The resulting differences telescope in the finite weighted reconstruction.

The formal theorem quantifies over all bases, positive real targets, admissible shifts, and digit positions. It is not a finite computation or a special-case example. No unproved mathematical assumption is added. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Install [elan](https://github.com/leanprover/elan), Python 3.9 or later, and Git. The checked-in configuration selects **Lean 4.30.0**, Mathlib commit **c5ea00351c28e24afc9f0f84379aa41082b1188f**, and fixed transitive dependency commits. No workspace paths or wrapper scripts are required.

```sh
lake exe cache get Mathlib.Algebra.Order.Floor.Ring Mathlib.Analysis.SpecialFunctions.Log.Base Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
python3 verify.py --clean
```

The verifier rebuilds the project with warnings treated as failures, requires all seven named axiom audits, rejects axioms outside the allowlist, and runs `leanchecker --fresh --verbose Jsp391`. It also checks dependency checkout commits and tracked-file cleanliness. Logs and a receipt containing exact source hashes and checkout information are written to `verification/current/`; the committed contributor-run local evidence is in [verification/local/](verification/local/).

Fresh replay uses the official Lean kernel and checks imported as well as local declarations. It is not a second independent implementation of the kernel. The [GitHub Actions workflow](.github/workflows/verify.yml) repeats these checks on Ubuntu and retains artifacts for 90 days. Reported verification applies to the source hashes recorded in each receipt; a configured workflow alone is not a successful run.

This repository's original code, scripts, and documentation use the [MIT license](LICENSE). See [NOTICE.md](NOTICE.md) for attribution and the distinction between contributor-run verification and independent review.
