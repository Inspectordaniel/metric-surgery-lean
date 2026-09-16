import Tablet.Preamble

open MeasureTheory Set

-- [TABLET NODE: Curve]
/-- A Lipschitz curve in `E`, parametrized by arc length on `[0, len]`, normalized to a
globally-defined function on all of `ℝ` by clamping outside `[0, len]`. -/
structure Curve (E : Type*) [MetricSpace E] where
-- BODY
  len : ℝ
  len_nonneg : 0 ≤ len
  toFun : ℝ → E
  clamped : ∀ t : ℝ, toFun t = toFun (min len (max 0 t))
  unitSpeed : HasUnitSpeedOn toFun (Set.Icc 0 len)
