import Tablet.IsGeodesicResolution

-- [TABLET NODE: IsPiecewiseGeodesicWith]
/-- `γ` admits a resolution into `k` geodesic edges (possibly with some degenerate, zero-length
edges): `γ` is a piecewise-geodesic curve expressible with `k` pieces. -/
def IsPiecewiseGeodesicWith {E : Type*} [MetricSpace E] (γ : Curve E) (k : ℕ) : Prop :=
-- BODY
  ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s
