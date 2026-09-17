# An atomic decomposition of one-dimensional metric currents without boundary

A Lean 4 formalization, against Mathlib, of all five main results of
[arXiv:2502.09871](https://arxiv.org/abs/2502.09871), "An atomic decomposition of
one-dimensional metric currents without boundary", by You-Wei Benson Chen, Jesse
Goodman, Felipe Hernandez and Daniel Spector.

Packaged for submission to the [Palomar registry](https://palomar-registry.org/).

## Repository map

- `Challenge.lean` — the advertised statement surface: the definitions the five results
  mention, then the five theorems stated with `sorry` bodies. It imports Mathlib and
  nothing else. This is the module to audit against the paper.
- `Solution.lean` — the same five declarations, with identical names and types, each
  proved by the corresponding theorem of `Tablet/`. No `sorry`, no new axioms.
- `Tablet/` — the proof development (133 modules).
- `comparator.json` — the declarations Comparator must compare.
- `scripts/` — the generator that keeps the two surfaces in step, and the two checks
  described under **Verification** below.
- `formalization.yaml` — project, source, authorship, automation, fidelity and review
  metadata.
- `LICENSE` — Apache License 2.0.

## How the two surfaces fit together

Comparator builds `Challenge.lean` and `Solution.lean` separately, into environments that
cannot see each other, and the canonical Palomar verifier goes further: it recompiles
`Challenge.lean` on its own, without this repository's Lake configuration and against the
allowlisted dependencies alone, under a per-run namespace of its own. So `Challenge.lean`
may not import `Tablet`, and `Solution.lean` may not import `Challenge`. Neither module
can borrow a definition from the other.

What Comparator then checks is that the five compared theorems have equal types *and*
that every constant reachable from those types is equal in both environments. The shared
notions — `Curve`, `Form1`, `MetricCurrent1`, `massOfFunctional`, `PSFamily`, `psi` and
the rest of their closure — therefore have to exist twice, at the same root-namespace
names, as the same declarations. In `Solution.lean` they are the `Tablet` declarations
themselves; in `Challenge.lean` they are a verbatim copy, generated from the same `Tablet`
node files by `scripts/gen-surface.py`, which also generates the five statements in both
modules from the `Tablet` theorem sources. `scripts/gen-surface.py --check` fails if any
of it has drifted, so the two copies cannot diverge unnoticed.

The compared declarations live in the `AtomicDecomposition` namespace, so that
`Challenge.lean` and `Solution.lean` can state them under one set of names while
`Solution.lean` also imports the identically-named root-namespace theorems of `Tablet/`.

## The five results

| Paper | Declaration |
| --- | --- |
| Theorem 1.1 | `AtomicDecomposition.ApproximationMetric` |
| Theorem 4.4 | `AtomicDecomposition.BBAssertion` |
| Corollary 3.2 | `AtomicDecomposition.SurgeryEta` |
| Corollary 2.6 | `AtomicDecomposition.C1SmallBall` |
| Corollary A.6 (ψ display) | `AtomicDecomposition.EtaRepeats` |

`PLAIN_LANGUAGE.md` gives a plain-language account of what each one says.

## Citation hypotheses

Two results that the paper cites rather than proves are carried as explicit hypotheses
of Theorems 1.1 and 4.4, rather than as axioms, so that nothing is assumed silently:

- `MassSupFormulaStatement E` — Ambrosio–Kirchheim Proposition 2.7, the hard direction
  of the mass supremum formula.
- `PaoliniStepanovExistsStatement E` — Paolini–Stepanov Theorem 3.1 with Proposition
  4.2, existence of a mass-realizing family of curves.

Corollaries 2.6, 3.2 and A.6 are unconditional. Both hypotheses are ordinary `def`s with
docstrings, in `Tablet/MassSupFormula.lean` and `Tablet/PaoliniStepanovExists.lean`, and
`Challenge.lean` carries them in full so a reader can see exactly what is being assumed.

## Build

```
lake exe cache get
lake build
```

`lake build` builds `Tablet`, `Challenge` and `Solution`. The only expected warnings are
the five deliberate `declaration uses 'sorry'` warnings from `Challenge.lean`; the proof
development and `Solution.lean` contain no `sorry`.

To check the axiom dependencies:

```
lake env lean --stdin <<'LEAN'
import Solution
#print axioms AtomicDecomposition.ApproximationMetric
#print axioms AtomicDecomposition.BBAssertion
#print axioms AtomicDecomposition.SurgeryEta
#print axioms AtomicDecomposition.C1SmallBall
#print axioms AtomicDecomposition.EtaRepeats
LEAN
```

Each reports exactly `[propext, Classical.choice, Quot.sound]`.

## Verification

```
python3 scripts/gen-surface.py --check   # the two surfaces still match the Tablet sources
./scripts/check-challenge-standalone.sh  # Challenge.lean builds against the packages alone
./scripts/check-surface-match.sh         # the two environments agree, as Comparator requires
```

The first is a source check. The second compiles `Challenge.lean` with only
`.lake/packages/*` on the search path and no Lake configuration, which is how the
canonical verifier compiles it; a Challenge that builds only under `lake build` can still
fail there. The third reproduces Comparator's own comparison inside Lean — it walks the
closure of the five compared types in each environment and diffs the two structurally —
so it can be run without Go, Rust or a working Landrun sandbox.

## How the formalization was produced

The Lean development was produced with [Trellis](https://github.com/wpegden/trellis)
driving Claude: Sonnet for the worker bursts that write and repair proofs, and Opus for
the reviewer and for the correspondence, faithfulness, substantiveness and soundness
verifiers. Every Lean proof is machine-checked by the Lean 4 kernel. The human
contribution is mathematical rather than tactic-level: the five theorem statements and
the two citation hypotheses were reviewed by the author, who is also an author of the
paper. The preprint is under review and not yet accepted for publication, and the
formalization has not been independently peer reviewed.

`formalization.yaml` records the deliberate divergences from the paper — chiefly that
the universal constants are pinned to numerals (2088, 522, c = 1/15) rather than left
existential, and that Corollary 2.6 is stated for an arbitrary metric space.

## License

Apache License 2.0; see `LICENSE`. The cited paper and the dependencies retain their own
licenses.
