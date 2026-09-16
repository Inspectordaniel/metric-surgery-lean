import Tablet.Preamble

open Set

-- [TABLET NODE: ShortWindowAtMostOneLongEdge]
/-- At most one index of a monotone breakpoint sequence `sA` can carry a long edge inside a short
interior window: if `sA` is monotone on `{0,…,K}` and its interior window `[sA 1, sA (K-1)]` has
length at most `δ > 0`, then at most one interior index `i ∈ {2,…,K-1}` has
`δ ≤ sA i - sA (i-1)`. Two such indices would contribute two disjoint sub-intervals of total
length at least `2δ` to a window of length at most `δ`. This is the half of
`ArcShortWindowEdgeCount`'s counting that needs no correspondence with the ambient curve: it is a
statement about the breakpoint sequence alone. Natural-number subtraction is used throughout, so
the index set is empty when `K ≤ 2`. -/
theorem ShortWindowAtMostOneLongEdge (K : ℕ) (sA : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hmono : MonotoneOn sA (Set.Icc 0 K))
    (hshort : sA (K - 1) - sA 1 ≤ δ) :
    ((Finset.Icc 2 (K - 1)).filter (fun i => δ ≤ sA i - sA (i - 1))).card ≤ 1 := by
-- BODY
  have m : ∀ a b : ℕ, a ≤ b → b ≤ K → sA a ≤ sA b := by
    intro a b hab hb
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hb⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb⟩) hab
  have key : ∀ x y : ℕ, 2 ≤ x → x ≤ K - 1 → 2 ≤ y → y ≤ K - 1 →
      δ ≤ sA x - sA (x - 1) → δ ≤ sA y - sA (y - 1) → x < y → False := by
    intro x y hx2 hxK hy2 hyK hxl hyl hxy
    have h1 : sA x ≤ sA (y - 1) := m x (y - 1) (by omega) (by omega)
    have h2 : sA 1 ≤ sA (x - 1) := m 1 (x - 1) (by omega) (by omega)
    have h3 : sA y ≤ sA (K - 1) := m y (K - 1) (by omega) (by omega)
    linarith
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
  obtain ⟨⟨hx2, hxK⟩, hxl⟩ := hx
  obtain ⟨⟨hy2, hyK⟩, hyl⟩ := hy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (key x y hx2 hxK hy2 hyK hxl hyl h) not_false
  · exact h
  · exact absurd (key y x hy2 hyK hx2 hxK hyl hxl h) not_false
