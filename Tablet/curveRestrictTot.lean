import Tablet.curveRestrict

-- [TABLET NODE: curveRestrictTot]
/-- The total, clamped restriction of a curve to `[a,b]`: agrees with `curveRestrict` whenever
`0 ≤ a ≤ b ≤ γ.len` (see `CurveRestrictTotAgrees`), and is otherwise a junk-but-total value
obtained by first clamping `a,b` into `[0, γ.len]` (and clamping `b` above `a`) before restricting.
This total version is what measure-theoretic statements (which only get `a,b` satisfying the
side conditions almost everywhere) must use instead of the proof-carrying `curveRestrict`. -/
noncomputable def curveRestrictTot {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ) :
    Curve E :=
-- BODY
  curveRestrict γ (min (max a 0) γ.len) (max (min (max a 0) γ.len) (min (max b 0) γ.len))
    (le_min (le_max_right _ _) γ.len_nonneg) (le_max_left _ _)
    (max_le (min_le_right _ _) (min_le_right _ _))
