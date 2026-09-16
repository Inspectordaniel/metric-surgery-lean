import Tablet.massOfFunctional
import Tablet.MetricCurrent1

open MeasureTheory ENNReal

-- [TABLET NODE: MassPosOfNonzero]
/-- `𝕄(T) ≠ 0` for a nonzero functional: if the infimum over admissible measures were `0`, every
`T ω` would be forced to `0`. -/
theorem MassPosOfNonzero {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (hT : T ≠ 0) : massOfFunctional T ≠ 0 := by
-- BODY
  intro h0
  apply hT
  funext ω
  have key : ∀ μ : { μ : Measure E // IsAdmissible T μ },
      ENNReal.ofReal |T ω| ≤ (ω.piLip : ℝ≥0∞) * (ω.fBound : ℝ≥0∞) * (μ.1 Set.univ) := by
    intro μ
    refine le_trans (μ.2.2 ω) ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc ∫⁻ x, ENNReal.ofReal |ω.f x| ∂(μ.1)
        ≤ ∫⁻ _x, ((ω.fBound : ℝ≥0∞)) ∂(μ.1) := by
          refine lintegral_mono fun x => ?_
          simpa using ENNReal.ofReal_le_ofReal (ω.f_bounded x)
      _ = (ω.fBound : ℝ≥0∞) * (μ.1 Set.univ) := by
          rw [lintegral_const]
  haveI hne : Nonempty { μ : Measure E // IsAdmissible T μ } := by
    by_contra hemp
    have : IsEmpty { μ : Measure E // IsAdmissible T μ } := not_nonempty_iff.mp hemp
    rw [massOfFunctional, iInf_of_empty] at h0
    exact (by simp : (⊤ : ℝ≥0∞) ≠ 0) h0
  have hcne : ((ω.piLip : ℝ≥0∞) * (ω.fBound : ℝ≥0∞)) ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  have : ENNReal.ofReal |T ω| ≤ (ω.piLip : ℝ≥0∞) * (ω.fBound : ℝ≥0∞) * massOfFunctional T := by
    rw [massOfFunctional, ENNReal.mul_iInf (fun htop => absurd htop hcne)]
    exact le_iInf key
  rw [h0, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  have : |T ω| = 0 := le_antisymm this (abs_nonneg _)
  simpa using abs_eq_zero.mp this
