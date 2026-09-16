import Tablet.RestrictPiecewiseGeodesic
import Tablet.IsDeltaEpsN

open Set

-- [TABLET NODE: RestrictDeltaEpsNAtBreakpoints]
/-- Restricting `γ` to the window between two breakpoints `s p, s q` of a geodesic resolution
`(k,s)` that linearly counts small edges is again a `(δ,ε,n)`-curve, provided the restricted arc
is non-closed (which discharges the closed-curve wrap clause of `IsDeltaEpsN` vacuously). The
general (non-breakpoint) restriction fails this inheritance: a restriction that truncates an edge
of `s` mid-edge can create a short edge for every `δ > 0` regardless of `n`. -/
theorem RestrictDeltaEpsNAtBreakpoints {E : Type*} [MetricSpace E] (γ : Curve E)
    (δ ε : ℝ) (n k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s)
    (hcount : ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ γ.len → t' - t ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => t ≤ s (j - 1) ∧ s j ≤ t' ∧ s j - s (j - 1) < δ)).card ≤ n)
    (p q : ℕ) (hpq : p ≤ q) (hqk : q ≤ k)
    (ha : 0 ≤ s p) (hab : s p ≤ s q) (hb : s q ≤ γ.len)
    (hnc : ¬ IsClosedCurve (curveRestrict γ (s p) (s q) ha hab hb)) :
    IsDeltaEpsN (curveRestrict γ (s p) (s q) ha hab hb) δ ε n := by
-- BODY
  refine ⟨q - p, fun j => s (p + j) - s p,
    RestrictPiecewiseGeodesic γ k s hres p q hpq hqk ha hab hb, ?_, ?_⟩
  · intro a b ha0 hab' hblen hlen
    have hlenR : (curveRestrict γ (s p) (s q) ha hab hb).len = s q - s p := rfl
    rw [hlenR] at hblen
    refine le_trans ?_ (hcount (a + s p) (b + s p) (by linarith) (by linarith)
      (by linarith) (by linarith))
    refine Finset.card_le_card_of_injOn (fun j => p + j) ?_ ?_
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj'.1
      obtain ⟨hA, hB, hC⟩ := hj'.2
      have hsub : p + j - 1 = p + (j - 1) := by omega
      have hmem : (fun (j : ℕ) => p + j) j ∈ Finset.Icc 1 k := by
        show p + j ∈ Finset.Icc 1 k
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      refine Finset.mem_filter.mpr ⟨hmem, ?_, ?_, ?_⟩
      · show a + s p ≤ s (p + j - 1)
        rw [hsub]; simp only at hA; linarith
      · show s (p + j) ≤ b + s p
        simp only at hB; linarith
      · show s (p + j) - s (p + j - 1) < δ
        rw [hsub]; simp only at hC; linarith
    · intro x _ y _ h
      exact Nat.add_left_cancel h
  · intro hcl
    exact absurd hcl hnc
