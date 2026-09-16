import Tablet.IsGeodesicResolution
import Tablet.IsPiecewiseGeodesic
import Tablet.MinimizingResolutionStrict
import Tablet.smallPieceCount

open Set

-- [TABLET NODE: StrictResolutionExists]
/-- Every piecewise-geodesic curve of positive length admits a strictly increasing (non-degenerate)
resolution into geodesic edges. -/
theorem StrictResolutionExists {E : Type*} [MetricSpace E] (γ : Curve E)
    (hpg : IsPiecewiseGeodesic γ) (hlen : 0 < γ.len) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧ ∀ i < k, s i < s (i + 1) := by
-- BODY
  obtain ⟨k0, s0, hres0⟩ := hpg
  -- the small-edge counts at scale `δ = 1`, over all resolutions of `γ`
  have key : smallPieceCount γ 1 ∈ { c : ℕ | ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
      c = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < (1 : ℝ))).card } :=
    Nat.sInf_mem ⟨_, k0, s0, hres0, rfl⟩
  obtain ⟨k, s, hres, hcard⟩ := key
  -- a count-minimizing resolution has no degenerate edges
  have hstrict : StrictMonoOn s (Set.Icc 0 k) :=
    MinimizingResolutionStrict γ 1 one_pos k s hres hcard.symm
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      obtain ⟨-, hs0, hsk, -⟩ := hres
      rw [h, hs0] at hsk
      exact absurd hsk.symm (ne_of_gt hlen)
    · exact h
  refine ⟨k, hk, s, hres, ?_⟩
  intro i hi
  exact hstrict ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
