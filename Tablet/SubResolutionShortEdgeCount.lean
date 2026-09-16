import Tablet.Preamble

open Set

-- [TABLET NODE: SubResolutionShortEdgeCount]
/-- **Short-edge counts transport exactly along the shifted sub-resolution `j ↦ s (c+j) - s c`.**
`RestrictPiecewiseGeodesic` resolves the window `γ|_{[s c, s d]}` of a curve by the shifted,
re-based breakpoint sequence `j ↦ s (c+j) - s c` with `d - c` edges. This lemma says that the
number of short (length `< δ`) edges of that sub-resolution is *exactly* the number of short edges
of `s` whose index lies in `{c+1,…,d}`: the reindexing `j ↦ c + j` is a bijection
`{1,…,d-c} → {c+1,…,d}` and the common base point `s c` cancels out of every edge difference.
Unlike `ShiftedBreakpointShortEdgeCount` and `SplicedBreakpointShortEdgeCount`, which are
*windowed inequalities* (they bound a count inside a metric window `[a',b']` by a count of `s`),
this is an unconditional *identity* of unwindowed counts, which is what is needed to add up the
counts of several sub-resolutions and compare the total against `s`'s own count. -/
theorem SubResolutionShortEdgeCount (c d : ℕ) (s : ℕ → ℝ) (δ : ℝ) :
    ((Finset.Icc 1 (d - c)).filter
        (fun j => (s (c + j) - s c) - (s (c + (j - 1)) - s c) < δ)).card
      = ((Finset.Ioc c d).filter (fun i => s i - s (i - 1) < δ)).card := by
-- BODY
  classical
  have himg : (Finset.Ioc c d).filter (fun i => s i - s (i - 1) < δ)
      = ((Finset.Icc 1 (d - c)).filter
          (fun j => (s (c + j) - s c) - (s (c + (j - 1)) - s c) < δ)).image (fun j => c + j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨i - c, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have e1 : c + (i - c) = i := by omega
      have e2 : c + (i - c - 1) = i - 1 := by omega
      rw [e1, e2]
      linarith
    · rintro ⟨j, ⟨⟨hj1, hj2⟩, hj3⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have e2 : c + j - 1 = c + (j - 1) := by omega
      rw [e2]
      linarith
  have hinj : Function.Injective (fun j : ℕ => c + j) := fun a b h => Nat.add_left_cancel h
  rw [himg, Finset.card_image_of_injective _ hinj]
