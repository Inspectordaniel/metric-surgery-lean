import Tablet.Preamble

open Set

-- [TABLET NODE: ClampedLinearShortEdgeCount]
/-- The linear counting clause of a `(δ,ε,n)`-curve extends from window pairs `(a,b)` constrained
by `0 ≤ a ≤ b ≤ L` to *arbitrary* real pairs `(a,b)` subject only to the gap bound
`b - a ≤ 2ε⁻¹δ`. The point is that a breakpoint sequence `s` running monotonically inside `[0,L]`
cannot see the part of a window that sticks out of `[0,L]`: replacing `(a,b)` by the clamped pair
`(max a 0, min b L)` only enlarges the counted set while shrinking the gap, so the clause applied
at the clamped pair dominates the count at the original pair. Vacuously true when the counted set
is empty, which is the only case where the clamped pair can fail to be ordered. -/
theorem ClampedLinearShortEdgeCount (k n : ℕ) (δ ε L : ℝ) (s : ℕ → ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k))
    (hlow : ∀ j : ℕ, j ≤ k → 0 ≤ s j) (hhigh : ∀ j : ℕ, j ≤ k → s j ≤ L)
    (hlin : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ L → b - a ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)).card ≤ n)
    (a b : ℝ) (hab : b - a ≤ 2 * ε⁻¹ * δ) :
    ((Finset.Icc 1 k).filter
      (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)).card ≤ n := by
-- BODY
  rcases Finset.eq_empty_or_nonempty ((Finset.Icc 1 k).filter
      (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)) with he | ⟨j0, hj0⟩
  · rw [he]; simp
  · obtain ⟨hj0I, hj0a, hj0b, -⟩ := Finset.mem_filter.mp hj0
    obtain ⟨hj01, hj0k⟩ := Finset.mem_Icc.mp hj0I
    have hstep : s (j0 - 1) ≤ s j0 :=
      hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
        (Set.mem_Icc.mpr ⟨Nat.zero_le _, hj0k⟩) (by omega)
    have h1 : (0:ℝ) ≤ s (j0 - 1) := hlow _ (by omega)
    have h2 : s j0 ≤ L := hhigh _ hj0k
    have hga : (0:ℝ) ≤ max a 0 := le_max_right _ _
    have hgab : max a 0 ≤ min b L :=
      le_trans (max_le hj0a h1) (le_trans hstep (le_min hj0b h2))
    have hgb : min b L ≤ L := min_le_right _ _
    have hggap : min b L - max a 0 ≤ 2 * ε⁻¹ * δ := by
      have e1 : min b L ≤ b := min_le_left _ _
      have e2 : a ≤ max a 0 := le_max_left _ _
      linarith
    refine le_trans (Finset.card_le_card ?_) (hlin (max a 0) (min b L) hga hgab hgb hggap)
    intro j hj
    obtain ⟨hjI, hja, hjb, hjd⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjI
    exact Finset.mem_filter.mpr ⟨hjI, max_le hja (hlow _ (by omega)),
      le_min hjb (hhigh _ hjk), hjd⟩
