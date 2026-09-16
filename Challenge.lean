import Tablet.MetricCurrent1
import Tablet.BoundaryZero
import Tablet.massOfFunctional
import Tablet.MassSupFormula
import Tablet.PaoliniStepanovExists
import Tablet.GeodesicPairing
import Tablet.Curve
import Tablet.Form1
import Tablet.IsClosedCurve
import Tablet.IsPiecewiseGeodesic
import Tablet.IsPiecewiseGeodesicWith
import Tablet.curveCurrent
import Tablet.curveMeasure
import Tablet.morreyNorm
import Tablet.PSFamily
import Tablet.psi

/-!
# Advertised statements

The five main results of arXiv:2502.09871, "An atomic decomposition of one-dimensional
metric currents without boundary" (Chen, Goodman, Hernandez, Spector).

This module is the small, trusted surface a mathematical reader should audit against the
paper. It states the five results and nothing else: each body is a deliberate `sorry`, and
the proofs live in `Solution.lean`. The imports above are exactly the modules carrying the
definitions the statements mention; each of those definitions has a docstring fixing its
mathematical meaning.

The definitions used below are:

* `Curve E` -- a Lipschitz curve in `E`, parametrized by arc length on `[0, len]` and
  clamped to a total function `ℝ → E` outside that interval.
* `Form1 E` -- a metric `1`-form `ω = (f, π) ∈ 𝒟¹(E)`, a bounded Lipschitz `f` paired with
  a Lipschitz `π`.
* `MetricCurrent1 E` -- a metric `1`-current: a functional on `Form1 E` that is multilinear,
  continuous and local, with finite mass.
* `BoundaryZero T` -- the current `T` has vanishing boundary, `∂T = 0`.
* `massOfFunctional T` -- the mass `𝕄(T)`, the infimum of `μ(E)` over admissible measures `μ`.
* `curveCurrent γ` -- the current `[[γ]]` carried by the curve `γ`.
* `curveMeasure γ` -- the measure `‖γ‖` carried by the curve `γ`.
* `morreyNorm μ` -- the Morrey norm `sup_{x, r} μ(B(x, r)) / r` of a measure `μ`.
* `IsClosedCurve γ`, `IsPiecewiseGeodesic γ`, `IsPiecewiseGeodesicWith γ k` -- `γ` is closed,
  is a concatenation of finitely many geodesics, is a concatenation of at most `k` geodesics.
* `GeodesicPairing E` -- a choice of geodesic between each pair of points, i.e. the witness
  that `E` is a geodesic space.
* `PSFamily T` and `psi m Q ε C γ` -- the Paolini--Stepanov family of curves representing `T`
  together with its rescaled measures `eta l`, and the test functional `ψ_{m,Q,ε,C}` of
  Appendix A.

Two results the paper cites rather than proves appear as explicit hypotheses rather than as
axioms, so that nothing here is assumed silently:

* `MassSupFormulaStatement E` -- Ambrosio--Kirchheim Proposition 2.7, the hard direction of
  the mass supremum formula. Used by Theorem 1.1 and Theorem 4.4 only.
* `PaoliniStepanovExistsStatement E` -- Paolini--Stepanov Theorem 3.1 with Proposition 4.2,
  existence of a mass-realizing family of curves. Used by Theorem 1.1 and Theorem 4.4 only.

Corollaries 2.6, 3.2 and A.6 below are unconditional.
-/

open Set Filter Finset MeasureTheory ENNReal

namespace AtomicDecomposition

/-- **Theorem 1.1** (`ApproximationMetric`). Every boundaryless `1`-dimensional metric current
`T` on a complete, separable, geodesic metric space `E` is a limit of finite nonnegative
combinations of closed piecewise-geodesic curves, with total weight at most `(1 + ε)` times
the mass of `T` and each curve's Morrey norm at most `2088 / ε²`.

The paper's universal constant `C` is pinned here to the numeral `2088 = 4 · 522`. Because
the paper quantifies `C` universally, outside the data, pinning a concrete value is at least
as strong as the paper's existential form.

`[Nonempty E]` is needed because the conclusion asserts a total function `γ : ℕ → ℕ → Curve E`
while `Curve E` is uninhabited exactly when `E` is, and no other hypothesis forces `E`
nonempty (this statement, unlike Theorem 4.4, carries no `T ≠ 0` hypothesis). -/
theorem ApproximationMetric {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hbdry : BoundaryZero T.toFun)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (γ : ℕ → ℕ → Curve E) (lam : ℕ → ℕ → ℝ),
      (∀ n : ℕ, ∀ i < n, 0 ≤ lam n i) ∧
      (∀ n : ℕ, ∀ i < n, IsClosedCurve (γ n i)) ∧
      (∀ n : ℕ, ∀ i < n, IsPiecewiseGeodesic (γ n i)) ∧
      (∀ ω : Form1 E, Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, lam n i * (curveCurrent (γ n i) ω / (γ n i).len))
        atTop (nhds (T.toFun ω))) ∧
      (∀ n : ℕ, ∑ i ∈ Finset.range n, |lam n i|
          ≤ (1 + ε) * (massOfFunctional T.toFun).toReal) ∧
      (∀ n : ℕ, ∀ i < n,
          morreyNorm (curveMeasure (γ n i)) ≤ ENNReal.ofReal (2088 / ε ^ 2))
    := by
  sorry

/-- **Theorem 4.4** (`BBAssertion`). A nonzero boundaryless `1`-dimensional metric current `T`
on a complete, separable, geodesic metric space admits a normalized decomposition along a
doubly-indexed family of closed piecewise-geodesic curves `ghat l i` of length at most `2l`,
with `𝕄([[ghat l i]]) ≤ len (ghat l i)`, such that the normalized sums converge to `T ω` for
every `1`-form `ω` and the mass and length averages both tend to `1`. -/
theorem BBAssertion {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hT0 : T.toFun ≠ 0) (hbdry : BoundaryZero T.toFun) :
    ∃ (n : ℕ → ℕ) (ghat : ℕ → ℕ → Curve E),
      (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesic (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l,
        massOfFunctional (curveCurrent (ghat l i)) ≤ ENNReal.ofReal (ghat l i).len) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω)
          atTop (nhds (T.toFun ω))) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (massOfFunctional (curveCurrent (ghat l i))).toReal)
        atTop (nhds 1)) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (ghat l i).len)
        atTop (nhds 1))
    := by
  sorry

/-- **Corollary 3.2** (`SurgeryEta`). A closed piecewise-geodesic curve `γ` splits into
finitely many closed piecewise-geodesic curves carrying the same current, of total length at
most `(1 + η)` times the length of `γ`, each of Morrey norm at most `522 / η²`.

The paper's absolute constant `c` in the prescription `ε = cη`, `n = ⌈ε⁻²⌉` is pinned to
`1/15`, which is sharp at `η = 1` for this argument, and the universal constant `C'` is
pinned to the numeral `522`. -/
theorem SurgeryEta {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + η) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (522 / η ^ 2))
    := by
  sorry

/-- **Corollary 2.6** (`C1SmallBall`). A concatenation of at most `k` geodesics has Morrey
norm at most `2k`.

Stated for an arbitrary metric space, since the proof uses neither completeness, nor
separability, nor ambient geodesy. -/
theorem C1SmallBall {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞)
    := by
  sorry

/-- **Corollary A.6** (`EtaRepeats`), the `ψ` display: the rescaling identity relating the
measures `eta l` and `eta 1` of a Paolini--Stepanov family, tested against `ψ`.

The companion `ψ̃` display of the same corollary is formalized separately, as
`EtaRepeatsTilde` in the proof development, and is not part of this compared surface. -/
theorem EtaRepeats {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T)
    (m : ℕ) (hm : 0 < m) (Q : Finset E) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (l : ℕ) (hl : 0 < l) :
    ∫ γ, (l : ℝ)⁻¹ * psi (m * l) Q ε C γ ∂(F.eta l)
      = ∫ γ, psi m Q ε C γ ∂(F.eta 1)
    := by
  sorry

end AtomicDecomposition
