import Tablet.MorreySubadditive
import Tablet.MorreyResolutionAdditive
import Tablet.GeodesicMorreyLeTwo
import Tablet.IsPiecewiseGeodesicWith

open MeasureTheory Set ENNReal

-- [TABLET NODE: C1SmallBall]
theorem C1SmallBall {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞) := by
-- BODY
  obtain ⟨s, hmono, h0, hk, hgeo⟩ := hpw
  have hadd := MorreyResolutionAdditive γ k s hmono h0 hk
  rw [hadd]
  have hsub := MorreySubadditive (Finset.range k)
    (fun i => Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1)))))
  refine hsub.trans ?_
  have hterm : ∀ i ∈ Finset.range k,
      morreyNorm (Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1))))) ≤ 2 := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hi1k : i + 1 ≤ k := hik
    have hab : s i ≤ s (i + 1) :=
      hmono ⟨Nat.zero_le i, hik.le⟩ ⟨Nat.zero_le (i + 1), hi1k⟩ (Nat.le_succ i)
    have hbnd : s (i + 1) ≤ γ.len :=
      hk ▸ hmono ⟨Nat.zero_le (i + 1), hi1k⟩ ⟨Nat.zero_le k, le_refl k⟩ hi1k
    exact GeodesicMorreyLeTwo γ (s i) (s (i + 1)) hab hbnd (hgeo i hik)
  calc ∑ i ∈ Finset.range k,
        morreyNorm (Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1)))))
      ≤ ∑ _i ∈ Finset.range k, (2 : ℝ≥0∞) := Finset.sum_le_sum hterm
    _ = 2 * (k : ℝ≥0∞) := by rw [Finset.sum_const, Finset.card_range]; ring
