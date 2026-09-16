import Tablet.dGamma
import Tablet.IsPiecewiseGeodesic

open Set

-- [TABLET NODE: IsLSI]
/-- `γ` is `(δ,ε)`-large-scale-invertible: `γ` is piecewise geodesic, and any two parameters
`s,t ∈ [0,γ.len]` that are `δ`-separated in the circle distance `dGamma` are moved apart by at
least `ε` times that distance (non-strictly; see the node's `.tex` for why this reading, rather
than the paper's literal strict `>`, is the one the paper's own proofs use and establish). -/
def IsLSI {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ) : Prop :=
-- BODY
  IsPiecewiseGeodesic γ ∧
    ∀ s ∈ Set.Icc (0 : ℝ) γ.len, ∀ t ∈ Set.Icc (0 : ℝ) γ.len,
      δ ≤ dGamma γ s t → ε * dGamma γ s t ≤ dist (γ.toFun s) (γ.toFun t)
