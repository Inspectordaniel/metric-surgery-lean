# An atomic decomposition of one-dimensional metric currents without boundary

A Lean 4 formalization, against Mathlib, of all five main results of
[arXiv:2502.09871](https://arxiv.org/abs/2502.09871), "An atomic decomposition of
one-dimensional metric currents without boundary", by You-Wei Benson Chen, Jesse
Goodman, Felipe Hernandez and Daniel Spector.

Packaged for submission to the [Palomar registry](https://palomar-registry.org/).

## Repository map

- `Challenge.lean` — the advertised statement surface: the five theorems stated with
  `sorry` bodies, importing only the modules carrying the definitions they mention.
  This is the module to audit against the paper.
- `Solution.lean` — the same five declarations, with identical names and types, each
  proved by the corresponding theorem of `Tablet/`. No `sorry`, no new axioms.
- `Tablet/` — the proof development (133 modules).
- `comparator.json` — the declarations Comparator must compare.
- `formalization.yaml` — project, source, authorship, automation, fidelity and review
  metadata.
- `LICENSE` — Apache License 2.0.

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
`Challenge.lean` imports them so a reader can see exactly what is being assumed.

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
