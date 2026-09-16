import Tablet.Preamble

open Set

-- [TABLET NODE: ShiftedBreakpointShortEdgeCount]
/-- Transport of a windowed short-edge count along an affine reindexing of breakpoints. If the
breakpoints `sA i` for `i` in an index range `{p-1,…,q}` are obtained from those of a second
sequence `s` by a single index map `i ↦ i + c - d` (with `d + 1 ≤ p + c`, so no natural-number
truncation occurs on the range) and a single value shift `σ`, namely `sA i = s (i + c - d) + σ`
with `i + c - d ≤ k`, then each index `i ∈ {p,…,q}` whose edge `sA i - sA (i-1)` is shorter than
`δ` and which lies in the window `[a',b']` (i.e. `a' ≤ sA (i-1)` and `sA i ≤ b'`) maps, under
`i ↦ i + c - d`, to an index `j ∈ {1,…,k}` whose edge `s j - s (j-1)` is shorter than `δ` and
which lies in the shifted window `[a'-σ, b'-σ]`. Since that map is injective, any bound `n` on the
number of such `j` bounds the number of such `i`. The window `[a',b']` is an arbitrary parameter,
not the extreme window `[sA 1, sA (K-1)]`, which is what lets a consumer count inside a small
sub-window of a long breakpoint sequence. -/
theorem ShiftedBreakpointShortEdgeCount (k n p q c d : ℕ) (δ σ a' b' : ℝ) (s sA : ℕ → ℝ)
    (hp : 1 ≤ p) (hd : d + 1 ≤ p + c)
    (hcorr : ∀ i : ℕ, p - 1 ≤ i → i ≤ q → i + c - d ≤ k ∧ sA i = s (i + c - d) + σ)
    (hcount : ((Finset.Icc 1 k).filter
      (fun j => a' - σ ≤ s (j - 1) ∧ s j ≤ b' - σ ∧ s j - s (j - 1) < δ)).card ≤ n) :
    ((Finset.Icc p q).filter
      (fun i => a' ≤ sA (i - 1) ∧ sA i ≤ b' ∧ sA i - sA (i - 1) < δ)).card ≤ n := by
-- BODY
  refine le_trans (Finset.card_le_card_of_injOn (fun i => i + c - d) ?_ ?_) hcount
  · intro i hi
    obtain ⟨hiI, hlo, hhi, hshort⟩ := Finset.mem_filter.mp hi
    obtain ⟨hip, hiq⟩ := Finset.mem_Icc.mp hiI
    obtain ⟨hle, heq⟩ := hcorr i (by omega) hiq
    obtain ⟨-, heq'⟩ := hcorr (i - 1) (by omega) (by omega)
    have hidx : i + c - d - 1 = i - 1 + c - d := by omega
    have hA : s (i + c - d) = sA i - σ := by rw [heq]; ring
    have hB : s (i + c - d - 1) = sA (i - 1) - σ := by rw [hidx, heq']; ring
    show i + c - d ∈ Finset.filter
      (fun j => a' - σ ≤ s (j - 1) ∧ s j ≤ b' - σ ∧ s j - s (j - 1) < δ) (Finset.Icc 1 k)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_, ?_, ?_⟩
    · rw [hB]; linarith
    · rw [hA]; linarith
    · rw [hA, hB]; linarith
  · intro x hx y hy hxy
    obtain ⟨hxI, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨hyI, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    obtain ⟨hxp, -⟩ := Finset.mem_Icc.mp hxI
    obtain ⟨hyp, -⟩ := Finset.mem_Icc.mp hyI
    have hxy' : x + c - d = y + c - d := hxy
    omega
