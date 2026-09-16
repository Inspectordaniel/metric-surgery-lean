import Tablet.curveSampling
import Tablet.IsPiecewiseGeodesic
import Tablet.GeodesicIsPiecewiseGeodesic
import Tablet.ConcatPiecewiseGeodesic

open Set

-- [TABLET NODE: SamplingPiecewiseGeodesic]
/-- The piecewise-geodesic sampling `γ^δ` of `γ` is itself piecewise geodesic (paper.tex line 1233
Definition 4.3: `γ^δ` is built as a chain of geodesic edges, hence manifestly piecewise geodesic;
needed so `BBAssertion`/`ClosingUp` can supply the `IsPiecewiseGeodesic` half of the paper's
"piecewise-geodesic closed curves" conclusion). -/
theorem SamplingPiecewiseGeodesic {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) :
    IsPiecewiseGeodesic (curveSampling GP γ δ hδ0 hδlen) := by
-- BODY
  unfold curveSampling
  generalize (⌈γ.len / δ⌉₊ - 1) = n
  induction n with
  | zero => exact ⟨1, GeodesicIsPiecewiseGeodesic GP _ _⟩
  | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨m + 1, ?_⟩
      apply ConcatPiecewiseGeodesic _ _ ?_ m 1 hm (GeodesicIsPiecewiseGeodesic GP _ _)
      rw [GP.start_eq]
      exact @Subtype.prop _
        (fun c : Curve E => c.toFun c.len = γ.toFun (min (((k + 1 : ℕ) : ℝ) * δ) γ.len)) _
