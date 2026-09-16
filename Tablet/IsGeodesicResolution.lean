import Tablet.IsGeodesicOn

open Set

-- [TABLET NODE: IsGeodesicResolution]
/-- `s : ℕ → ℝ` is a resolution of `γ` into `k` geodesic edges: `s` is monotone on `{0,…,k}`,
runs from `0` to `γ.len`, and each consecutive pair of values bounds a geodesic edge of `γ`.
Consecutive values of `s` are allowed to repeat (a degenerate, zero-length edge). -/
def IsGeodesicResolution {E : Type*} [MetricSpace E] (γ : Curve E) (k : ℕ) (s : ℕ → ℝ) : Prop :=
-- BODY
  MonotoneOn s (Set.Icc 0 k) ∧ s 0 = 0 ∧ s k = γ.len ∧
    ∀ i < k, IsGeodesicOn γ (s i) (s (i + 1))
