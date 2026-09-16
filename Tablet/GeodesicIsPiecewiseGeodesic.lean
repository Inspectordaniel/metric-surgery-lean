import Tablet.GeodesicPairing
import Tablet.IsPiecewiseGeodesicWith

open Set

-- [TABLET NODE: GeodesicIsPiecewiseGeodesic]
/-- A geodesic pairing's chosen geodesic `G x y` is piecewise geodesic with exactly one edge
(paper.tex line 1441 / the surrounding discussion of `\hat\gamma_{i,l}` and `\bar\gamma_{i,l}`
being built from geodesics `G_{x,y}`, which the paper treats as visibly piecewise-geodesic). -/
theorem GeodesicIsPiecewiseGeodesic {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (x y : E) : IsPiecewiseGeodesicWith (GP.G x y) 1 := by
-- BODY
  classical
  refine ⟨fun j => if j = 0 then 0 else (GP.G x y).len, ?_, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · simp [hb]
      · simp [hb, (GP.G x y).len_nonneg]
    · have hb : b ≠ 0 := by rintro rfl; omega
      simp [ha, hb]
  · simp
  · simp
  · intro i hi
    interval_cases i
    · simpa using GP.isGeodesic x y
