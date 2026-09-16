import Tablet.Preamble

open Set

-- [TABLET NODE: StraddleAtMostOneEdge]
/-- Edges of a monotone breakpoint sequence have pairwise disjoint interiors, so a single real
number `c` lies in the open interior `(s (j-1), s j)` of at most one edge `j ∈ {1,…,k}`.
Natural-number subtraction is used for `j - 1`. -/
theorem StraddleAtMostOneEdge (k : ℕ) (s : ℕ → ℝ) (c : ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) :
    ((Finset.Icc 1 k).filter (fun j => s (j - 1) < c ∧ c < s j)).card ≤ 1 := by
-- BODY
  have hm : ∀ p q : ℕ, p ≤ q → q ≤ k → s p ≤ s q := by
    intro p q hpq hq
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hpq.trans hq⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
  obtain ⟨⟨hx1, hxk⟩, hxl, hxr⟩ := hx
  obtain ⟨⟨hy1, hyk⟩, hyl, hyr⟩ := hy
  by_contra hne
  rcases Nat.lt_or_ge x y with h | h
  · have hle : s x ≤ s (y - 1) := hm x (y - 1) (by omega) (by omega)
    linarith
  · have hxy : y < x := by omega
    have hle : s y ≤ s (x - 1) := hm y (x - 1) (by omega) (by omega)
    linarith
