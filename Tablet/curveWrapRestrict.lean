import Tablet.curveConcat
import Tablet.curveRestrict
import Tablet.IsClosedCurve

open Set

-- [TABLET NODE: curveWrapRestrict]
/-- The wrap-around restriction $\gamma|_{[t,t']}$ of a closed curve for $t' < t$ (paper lines
557-568): the concatenation of $\gamma|_{[t,\length(\gamma)]}$ with $\gamma|_{[0,t']}$, traversing
past the identified endpoint of the circle. -/
noncomputable def curveWrapRestrict {E : Type*} [MetricSpace E] (γ : Curve E) (t t' : ℝ)
    (hclosed : IsClosedCurve γ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht't : t' < t) :
    Curve E :=
-- BODY
  curveConcat (curveRestrict γ t γ.len ht0 htlen (le_refl _))
    (curveRestrict γ 0 t' (le_refl 0) ht'0 (by linarith))
    (by
      show γ.toFun (t + min (γ.len - t) (max 0 (γ.len - t)))
          = γ.toFun (0 + min (t' - 0) (max 0 0))
      have e1 : max (0:ℝ) (γ.len - t) = γ.len - t := max_eq_right (by linarith)
      have e2 : min (γ.len - t) (γ.len - t) = γ.len - t := min_self _
      have e3 : max (0:ℝ) (0:ℝ) = 0 := max_self 0
      have e4 : min (t' - 0) (0:ℝ) = 0 := by
        rw [sub_zero]; exact min_eq_right ht'0
      rw [e1, e2, e3, e4]
      have hz : t + (γ.len - t) = γ.len := by ring
      rw [hz, add_zero]
      exact hclosed)
