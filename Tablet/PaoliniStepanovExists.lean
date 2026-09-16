import Tablet.MetricCurrent1
import Tablet.BoundaryZero
import Tablet.PSFamily

open MeasureTheory ENNReal

-- [TABLET NODE: PaoliniStepanovExists]
/-- Paolini--Stepanov `[PS, Thm 3.1]` + `[PS, Prop 4.2]` (paper.tex 1183–1216): for a metric
`1`-current `T` on a complete separable `E` with `∂T = 0` (`BoundaryZero`) and `T ≠ 0`, there is a
Paolini–Stepanov family `F` for `T.toFun` (`PSFamily`) whose mass measure realizes the total mass
of `T` (paper.tex 1192, `M(T) = η_1(Θ_1(E))`, combined with `massOfFunctional`'s own
minimum-realizes-infimum equivalence).

This node is an external literature citation, not a tablet proof. It is therefore recorded as a
`Prop`-valued statement about `E` rather than as a theorem with an unproved body: the nodes that
consume it (`\noderef{BBAssertion}` and, through it, `\noderef{ApproximationMetric}`) take
`PaoliniStepanovExistsStatement E` as an explicit hypothesis. The citation is thereby discharged
by the caller, and the tablet's own theorems depend on no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`. -/
def PaoliniStepanovExistsStatement (E : Type*) [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] : Prop :=
  ∀ (T : MetricCurrent1 E), T.toFun ≠ 0 → BoundaryZero T.toFun →
    ∃ F : PSFamily T.toFun, F.massMeasure Set.univ = massOfFunctional T.toFun
