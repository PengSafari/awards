# Certificate generation

The final Lean build needs no external SAT solver. The source files already contain ordinary proofs of all required propositional clauses.

`generate_refutation.py` reads `data/n18.cnf` and `data/n18.drat`. A clause is represented by a curried implication from the negations of its literals to `False`. Each unit-propagation step constructs a literal proof from an earlier clause; positive literals use classical contradiction where necessary. A final conflicting clause derives `False`. The generated `Initial.lean` proves initial clauses from the exact mathematical hypotheses, and 31 `StepsNN.lean` files prove the retained learned clauses. `Jsp746/Refutation.lean` exposes the resulting theorem.

The generator is untrusted. Its output has to compile and survive kernel replay. The metadata in `refutation-generation.json` identifies the input hashes and exact counts.

From the repository root:

```sh
python3 scripts/check_data.py
python3 scripts/check_rup.py
python3 scripts/generate_refutation.py
python3 verify.py --clean
```

The Python RUP checker is separate from the proof generator and checks every trace addition by reverse unit propagation. It does not implement a RAT fallback and is not a formally verified checker. Its verdict is not imported into Lean. The data checker reconstructs both CNFs independently, checks the 42-edge witness, and confirms the saved trace hashes.

For an optional new discovery run, install [CaDiCaL](https://github.com/arminbiere/cadical), then use:

```sh
python3 scripts/search.py --solver cadical --output discovery
```

The executable can also be supplied through `CADICAL`. The output directory is separate from the checked-in `data/` by default. The original run used the CaDiCaL executable bundled with the local Lean 4.30.0 toolchain. Other solver builds can return different witnesses and proof traces; their outputs must be translated and rechecked before replacing a verified proof.

To use a new trace, explicitly copy its CNF/trace into `data/`, regenerate the proof, and run the complete verification command. The checked-in `Witness.lean` is not automatically replaced by a new SAT model. Keep its 42-edge list and `data/witness.json` consistent. The data checker detects disagreement.
