import Tablet.Curve
import Tablet.IsClosedCurve

open Classical

-- [TABLET NODE: dGamma]
/-- The circle distance $d_\gamma(t,t')$ (paper line 573, extended to non-closed curves at line
579): for a closed curve, the smaller of the two arc lengths between $t$ and $t'$; for a
non-closed curve, just $|t-t'|$. -/
noncomputable def dGamma {E : Type*} [MetricSpace E] (γ : Curve E) (t t' : ℝ) : ℝ :=
-- BODY
  if IsClosedCurve γ then min |t - t'| (γ.len - |t - t'|) else |t - t'|
