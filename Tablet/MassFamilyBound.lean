import Tablet.massOfFunctional
import Tablet.MetricCurrent1

open MeasureTheory ENNReal

-- [TABLET NODE: MassFamilyBound]
/-- The EASY half of Ambrosio–Kirchheim's mass–supremum formula: for any functional `T`, any
finite family of `1`-forms with `Lip(π_p) ≤ 1` and `∑_p |f_p| ≤ 1` pointwise satisfies
`∑_p |T(ω_p)| ≤ 𝕄(T)`. Free from `massOfFunctional`'s definition as an infimum over admissible
measures; no external citation. -/
theorem MassFamilyBound {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (n : ℕ) (ω : Fin n → Form1 E)
    (hpi : ∀ p, (ω p).piLip ≤ 1)
    (hf : ∀ x : E, ∑ p, |(ω p).f x| ≤ 1) :
    ENNReal.ofReal (∑ p, |T (ω p)|) ≤ massOfFunctional T := by
-- BODY
  rw [massOfFunctional]
  refine le_iInf fun μ => ?_
  obtain ⟨hfin, hadm⟩ := μ.2
  have hmeas : ∀ p, Measurable (fun x : E => ENNReal.ofReal |(ω p).f x|) := by
    intro p
    exact ENNReal.measurable_ofReal.comp
      (((ω p).f_lipschitz.continuous.abs).measurable)
  calc ENNReal.ofReal (∑ p, |T (ω p)|)
      = ∑ p, ENNReal.ofReal |T (ω p)| := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => abs_nonneg _)]
    _ ≤ ∑ p, ((ω p).piLip : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |(ω p).f x| ∂(μ.1) :=
        Finset.sum_le_sum (fun p _ => hadm (ω p))
    _ ≤ ∑ p, ∫⁻ x, ENNReal.ofReal |(ω p).f x| ∂(μ.1) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        have h1 : ((ω p).piLip : ℝ≥0∞) ≤ 1 := by
          exact_mod_cast ENNReal.coe_le_one_iff.mpr (hpi p)
        calc ((ω p).piLip : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |(ω p).f x| ∂(μ.1)
            ≤ 1 * ∫⁻ x, ENNReal.ofReal |(ω p).f x| ∂(μ.1) := by
              exact mul_le_mul' h1 le_rfl
          _ = ∫⁻ x, ENNReal.ofReal |(ω p).f x| ∂(μ.1) := one_mul _
    _ = ∫⁻ x, (∑ p, ENNReal.ofReal |(ω p).f x|) ∂(μ.1) := by
        rw [lintegral_finsetSum _ (fun p _ => hmeas p)]
    _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂(μ.1) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_one.mpr (hf x)
    _ = μ.1 Set.univ := by simp
