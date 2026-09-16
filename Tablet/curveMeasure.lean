import Tablet.Curve

open MeasureTheory Set

-- [TABLET NODE: curveMeasure]
/-- The Borel measure `μ_γ` on `E` induced by a curve `γ`: the pushforward, under `γ`, of
Lebesgue measure restricted to `[0, γ.len]` (paper eq. (2.1)). -/
noncomputable def curveMeasure {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) : Measure E :=
-- BODY
  Measure.map γ.toFun (volume.restrict (Set.Icc 0 γ.len))
