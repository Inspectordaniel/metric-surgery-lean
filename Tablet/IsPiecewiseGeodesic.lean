import Tablet.IsPiecewiseGeodesicWith

-- [TABLET NODE: IsPiecewiseGeodesic]
/-- `γ` is a piecewise-geodesic curve: it admits a resolution into `k` geodesic edges for some `k`. -/
def IsPiecewiseGeodesic {E : Type*} [MetricSpace E] (γ : Curve E) : Prop :=
-- BODY
  ∃ k : ℕ, IsPiecewiseGeodesicWith γ k
