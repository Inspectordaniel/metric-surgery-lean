import Tablet.Curve

open Set

-- [TABLET NODE: IsGeodesicOn]
/-- `γ` is a geodesic on the subinterval `[a,b]` of its domain: `γ` is an isometric embedding of
`[a,b]` into `E` there. -/
def IsGeodesicOn {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ) : Prop :=
-- BODY
  ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, dist (γ.toFun s) (γ.toFun t) = |s - t|
