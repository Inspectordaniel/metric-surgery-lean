import Tablet.curveCurrent
import Tablet.curveRestrict
import Tablet.CurrentConcatAdditive

open Set MeasureTheory

-- [TABLET NODE: RestrictCurrentFormula]
/-- The current of a restriction, computed as the un-reparametrized integral over the original
domain: this is what lets `CurrentResolutionAdditive`'s un-reparametrized resolution sum be read as
a sum of currents of the restricted pieces. -/
theorem RestrictCurrentFormula {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) (ω : Form1 E) :
    curveCurrent (curveRestrict γ a b ha hab hb) ω
      = ∫ t in a..b, ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t := by
-- BODY
  have hba : (0:ℝ) ≤ b - a := by linarith
  -- The underlying data of the restriction, definitionally.
  have hlen : (curveRestrict γ a b ha hab hb).len = b - a := rfl
  have hval : ∀ u : ℝ, (curveRestrict γ a b ha hab hb).toFun u
      = γ.toFun (a + min (b - a) (max 0 u)) := fun _ => rfl
  -- On the open interval `(0, b - a)` the clamping is inert.
  have hEq : ∀ u ∈ Ioo (0:ℝ) (b - a),
      (curveRestrict γ a b ha hab hb).toFun u = γ.toFun (a + u) := by
    intro u hu
    rw [hval u, max_eq_right hu.1.le, min_eq_right hu.2.le]
  -- Step 1: the derivatives agree on `(0, b - a)`, via the additive shift identity.
  have hderiv : ∀ u ∈ Ioo (0:ℝ) (b - a),
      deriv (ω.pi ∘ (curveRestrict γ a b ha hab hb).toFun) u
        = deriv (ω.pi ∘ γ.toFun) (a + u) := by
    intro u hu
    have h1 : deriv (ω.pi ∘ (curveRestrict γ a b ha hab hb).toFun) u
        = deriv (fun v => (ω.pi ∘ γ.toFun) (a + v)) u := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
      simp only [Function.comp_apply, hEq v hv]
    rw [h1, deriv_comp_const_add]
  -- Steps 2-3: the integrands agree off the single point `u = b - a`, a null set.
  have hcongr : curveCurrent (curveRestrict γ a b ha hab hb) ω
      = ∫ u in (0:ℝ)..(b - a), ω.f (γ.toFun (a + u)) * deriv (ω.pi ∘ γ.toFun) (a + u) := by
    rw [curveCurrent, hlen]
    refine intervalIntegral.integral_congr_ae ?_
    have hae : ∀ᵐ x : ℝ ∂volume, x ≠ b - a := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hae] with x hx hxmem
    rw [Set.uIoc_of_le hba] at hxmem
    have hxIoo : x ∈ Ioo (0:ℝ) (b - a) := ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx⟩
    rw [hderiv x hxIoo, hEq x hxIoo]
  -- Step 4: translate the integration variable by `a`.
  rw [hcongr]
  have hshift := intervalIntegral.integral_comp_add_left
    (a := (0:ℝ)) (b := b - a)
    (fun t => ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t) a
  have harith : a + (b - a) = b := by ring
  rw [harith, add_zero] at hshift
  exact hshift
