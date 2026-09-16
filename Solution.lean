import Tablet.ApproximationMetric
import Tablet.BBAssertion
import Tablet.SurgeryEta
import Tablet.C1SmallBall
import Tablet.EtaRepeats

/-!
# Proved solutions

The same five declarations as `Challenge.lean`, with identical names and identical types,
each discharged by the corresponding theorem of the `Tablet` proof development. No `sorry`
and no new axioms: every declaration below depends only on `propext`, `Classical.choice` and
`Quot.sound`.

The `Tablet` theorems live in the root namespace, so they are referred to below as
`_root_.ApproximationMetric` and so on, and the advertised declarations are placed in the
`AtomicDecomposition` namespace to keep the two sets of names distinct.
-/

open Set Filter Finset MeasureTheory ENNReal

namespace AtomicDecomposition

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
    :=
  _root_.ApproximationMetric hAK hPS GP T hbdry ε hε0 hε1

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
    :=
  _root_.BBAssertion hAK hPS GP T hT0 hbdry

theorem SurgeryEta {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + η) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (522 / η ^ 2))
    :=
  _root_.SurgeryEta GP γ η hη0 hη1 hclosed hpg

theorem C1SmallBall {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞)
    :=
  _root_.C1SmallBall γ k hpw

theorem EtaRepeats {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T)
    (m : ℕ) (hm : 0 < m) (Q : Finset E) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (l : ℕ) (hl : 0 < l) :
    ∫ γ, (l : ℝ)⁻¹ * psi (m * l) Q ε C γ ∂(F.eta l)
      = ∫ γ, psi m Q ε C γ ∂(F.eta 1)
    :=
  _root_.EtaRepeats T F m hm Q ε C hε hC l hl

end AtomicDecomposition
