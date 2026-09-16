import Tablet.curveCurrent
import Tablet.CurveLipschitz

open scoped NNReal

-- [TABLET NODE: CurveCurrentBound]
theorem CurveCurrentBound {E : Type*} [MetricSpace E] (γ : Curve E) (ω : Form1 E) :
    |curveCurrent γ ω| ≤ (ω.fBound : ℝ) * (ω.piLip : ℝ) * γ.len := by
-- BODY
  have hlip : LipschitzWith ω.piLip (ω.pi ∘ γ.toFun) := by
    have h := ω.pi_lipschitz.comp (CurveLipschitz γ)
    simpa using h
  have hbound : ∀ t : ℝ, |ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t| ≤ (ω.fBound : ℝ) * (ω.piLip : ℝ) := by
    intro t
    rw [abs_mul]
    by_cases hd : DifferentiableAt ℝ (ω.pi ∘ γ.toFun) t
    · have hderiv_le : |deriv (ω.pi ∘ γ.toFun) t| ≤ (ω.piLip : ℝ) := by
        have h := hd.hasDerivAt.le_of_lipschitz hlip
        simpa using h
      exact mul_le_mul (ω.f_bounded (γ.toFun t)) hderiv_le (abs_nonneg _)
        (le_trans (abs_nonneg _) (ω.f_bounded (γ.toFun t)))
    · rw [deriv_zero_of_not_differentiableAt hd]
      simpa using mul_nonneg (ω.fBound.coe_nonneg) (ω.piLip.coe_nonneg)
  have hlen : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hkey : |curveCurrent γ ω| ≤ (ω.fBound : ℝ) * (ω.piLip : ℝ) * |γ.len - 0| := by
    unfold curveCurrent
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := γ.len)
      (f := fun t => ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t)
      (C := (ω.fBound : ℝ) * (ω.piLip : ℝ))
      (fun t _ => by simpa using hbound t)
    simpa using this
  simpa [sub_zero, abs_of_nonneg hlen] using hkey
