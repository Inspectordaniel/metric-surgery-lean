import Tablet.Curve

-- [TABLET NODE: IsClosedCurve]
/-- `γ` is a closed curve: its two endpoints coincide. -/
def IsClosedCurve {E : Type*} [MetricSpace E] (γ : Curve E) : Prop :=
-- BODY
  γ.toFun γ.len = γ.toFun 0
