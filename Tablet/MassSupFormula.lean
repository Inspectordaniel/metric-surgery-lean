import Tablet.MetricCurrent1

open MeasureTheory ENNReal

-- [TABLET NODE: MassSupFormula]
/-- Ambrosio--Kirchheim `[AK, Prop. 2.7]` (paper.tex ~1497--1501), hard direction only, indexed
over finite families: if every finite family `ω : Fin n → Form1 E` with `Lip(π_p) ≤ 1` for all `p`
and `∑_p |f_p(x)| ≤ 1` for every `x` has `∑_p |T(ω p)| ≤ c`, then `massOfFunctional T.toFun ≤
ENNReal.ofReal c`. The reverse direction `sup ≤ massOfFunctional T.toFun` is free from the
definition of `massOfFunctional` as an infimum and is proved inline at each use site rather than
cited here. `[CompleteSpace E] [TopologicalSpace.SeparableSpace E]` discharge the paper's standing
ambient hypothesis on `E` (paper.tex line 1096) under which AK Prop. 2.7 is invoked; geodesy is
deliberately not assumed, since Prop. 2.7 is a statement about `M₁(E)` with no reference to
geodesics.

This node is an external literature citation, not a tablet proof. It is therefore recorded as a
`Prop`-valued statement about `E` rather than as a theorem with an unproved body: the nodes that
consume it (`\noderef{BBAssertion}` and, through it, `\noderef{ApproximationMetric}`) take
`MassSupFormulaStatement E` as an explicit hypothesis. The citation is thereby discharged by the
caller, and the tablet's own theorems depend on no axioms beyond `propext`, `Classical.choice`
and `Quot.sound`. -/
def MassSupFormulaStatement (E : Type*) [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] : Prop :=
  ∀ (T : MetricCurrent1 E) (c : ℝ), 0 ≤ c →
    (∀ (n : ℕ) (ω : Fin n → Form1 E),
      (∀ p, (ω p).piLip ≤ 1) →
      (∀ x : E, ∑ p, |(ω p).f x| ≤ 1) →
      ∑ p, |T.toFun (ω p)| ≤ c) →
    massOfFunctional T.toFun ≤ ENNReal.ofReal c
