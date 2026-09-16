import Tablet.Preamble

open Set

-- [TABLET NODE: ConcatResolutionShortEdgeCount]
/-- **Short-edge counts are additive across a glued resolution.** `ConcatGeodesicResolution`
resolves a concatenation `η₁ * η₂` by the spliced breakpoint sequence `R i = r₁ i` for `i ≤ K₁` and
`R i = L + r₂ (i - K₁)` for `i > K₁`, where `L = length(η₁) = r₁ K₁` and `r₂ 0 = 0`. This lemma
says that the number of short (length `< δ`) edges of `R` is *exactly* the sum of the numbers of
short edges of `r₁` and of `r₂`: the two index blocks `{1,…,K₁}` and `{K₁+1,…,K₁+K₂}` partition
`{1,…,K₁+K₂}`, the shift `L` cancels out of every edge difference on the upper block, and the one
straddling index `i = K₁+1` gives the edge `L + r₂ 1 - r₁ K₁ = r₂ 1 - r₂ 0` because `r₁ K₁ = L`
and `r₂ 0 = 0`. `ConcatGeodesicResolution` asserts only that the glued object *is* a resolution; it
says nothing about edge counts, which is the entire content here. Applied with `K₂ = 1` it gives
the "at most one extra short edge for the single closing geodesic edge" bound that a basic cut's
output needs. -/
theorem ConcatResolutionShortEdgeCount (K₁ K₂ : ℕ) (r₁ r₂ R : ℕ → ℝ) (L δ : ℝ)
    (hL : r₁ K₁ = L) (hz : r₂ 0 = 0)
    (hR : ∀ i : ℕ, R i = if i ≤ K₁ then r₁ i else L + r₂ (i - K₁)) :
    ((Finset.Icc 1 (K₁ + K₂)).filter (fun i => R i - R (i - 1) < δ)).card
      = ((Finset.Icc 1 K₁).filter (fun j => r₁ j - r₁ (j - 1) < δ)).card
        + ((Finset.Icc 1 K₂).filter (fun j => r₂ j - r₂ (j - 1) < δ)).card := by
-- BODY
  classical
  have key1 : ∀ i : ℕ, 1 ≤ i → i ≤ K₁ → R i - R (i - 1) = r₁ i - r₁ (i - 1) := by
    intro i h1 h2
    rw [hR i, hR (i - 1), if_pos h2, if_pos (by omega)]
  have keyA : ∀ j : ℕ, 1 ≤ j → R (K₁ + j) = L + r₂ j := by
    intro j h1
    rw [hR, if_neg (by omega)]
    have e : K₁ + j - K₁ = j := by omega
    rw [e]
  have keyB : ∀ j : ℕ, 1 ≤ j → R (K₁ + j - 1) = L + r₂ (j - 1) := by
    intro j h1
    rw [hR]
    by_cases hj : K₁ + j - 1 ≤ K₁
    · rw [if_pos hj]
      have e : K₁ + j - 1 = K₁ := by omega
      rw [e, hL]
      have e2 : j - 1 = 0 := by omega
      rw [e2, hz, add_zero]
    · rw [if_neg hj]
      have e : K₁ + j - 1 - K₁ = j - 1 := by omega
      rw [e]
  have key2 : ∀ j : ℕ, 1 ≤ j → R (K₁ + j) - R (K₁ + j - 1) = r₂ j - r₂ (j - 1) := by
    intro j h1
    rw [keyA j h1, keyB j h1]
    ring
  have hinj : Function.Injective (fun j : ℕ => K₁ + j) := fun a b h => Nat.add_left_cancel h
  have hsplit : (Finset.Icc 1 (K₁ + K₂)).filter (fun i => R i - R (i - 1) < δ)
      = ((Finset.Icc 1 K₁).filter (fun j => r₁ j - r₁ (j - 1) < δ))
        ∪ (((Finset.Icc 1 K₂).filter (fun j => r₂ j - r₂ (j - 1) < δ)).image
            (fun j => K₁ + j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hi : i ≤ K₁
      · exact Or.inl ⟨⟨h1, hi⟩, by rw [← key1 i h1 hi]; exact h3⟩
      · refine Or.inr ⟨i - K₁, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
        have e : K₁ + (i - K₁) = i := by omega
        rw [← key2 (i - K₁) (by omega), e]
        exact h3
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨j, ⟨⟨hj1, hj2⟩, hj3⟩, rfl⟩)
      · exact ⟨⟨h1, by omega⟩, by rw [key1 i h1 h2]; exact h3⟩
      · exact ⟨⟨by omega, by omega⟩, by rw [key2 j hj1]; exact hj3⟩
  have hdisj : Disjoint ((Finset.Icc 1 K₁).filter (fun j => r₁ j - r₁ (j - 1) < δ))
      (((Finset.Icc 1 K₂).filter (fun j => r₂ j - r₂ (j - 1) < δ)).image (fun j => K₁ + j)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨haI, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp haI
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp hb
    obtain ⟨hjI, -⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hjI
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj]
