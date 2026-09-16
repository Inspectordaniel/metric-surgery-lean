import Tablet.IsGeodesicResolution
import Tablet.IsClosedCurve

open Set

-- [TABLET NODE: IsDeltaEpsN]
/-- `γ` is a `(δ,ε,n)`-curve: it has a resolution into geodesic edges such that (i) every genuine
subinterval `[t,t']` of `[0,γ.len]` of length at most `2ε⁻¹δ` contains at most `n` edges of that
resolution of length less than `δ`, and (ii) — when `γ` is closed — the same bound holds for every
circle arc `[t,γ.len] ∪ [0,t']` of length at most `2ε⁻¹δ`. -/
def IsDeltaEpsN {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ) (n : ℕ) : Prop :=
-- BODY
  ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
    (∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ γ.len → t' - t ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => t ≤ s (j - 1) ∧ s j ≤ t' ∧ s j - s (j - 1) < δ)).card ≤ n) ∧
    (IsClosedCurve γ → ∀ t t' : ℝ, 0 ≤ t' → t' < t → t ≤ γ.len →
      (γ.len - t) + t' ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => (t ≤ s (j - 1) ∨ s j ≤ t') ∧ s j - s (j - 1) < δ)).card ≤ n)
