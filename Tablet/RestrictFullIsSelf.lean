import Tablet.curveRestrict

open Set

-- [TABLET NODE: RestrictFullIsSelf]
/-- Restricting a curve `A` to its own full domain `[0, A.len]` recovers `A` itself. -/
theorem RestrictFullIsSelf {E : Type*} [MetricSpace E] (A : Curve E) :
    curveRestrict A 0 A.len (le_refl 0) A.len_nonneg (le_refl A.len) = A := by
-- BODY
  have hfun : (fun u => A.toFun (0 + min (A.len - 0) (max 0 u))) = A.toFun := by
    funext u
    show A.toFun (0 + min (A.len - 0) (max 0 u)) = A.toFun u
    rw [zero_add, sub_zero]
    exact (A.clamped u).symm
  cases A with
  | mk len hnn f hcl hus =>
    simp only [curveRestrict, sub_zero] at *
    congr 1
