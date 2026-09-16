import Tablet.IsGeodesicResolution

open Set

-- [TABLET NODE: smallPieceCount]
/-- The number of short (length `< δ`) geodesic edges in `γ`, minimized over all resolutions of
`γ` into geodesic edges. -/
noncomputable def smallPieceCount {E : Type*} [MetricSpace E] (γ : Curve E) (δ : ℝ) : ℕ :=
-- BODY
  sInf { c : ℕ | ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
    c = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card }
