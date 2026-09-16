import Tablet.psiTilde
import Tablet.CurveLenMeasurable
import Tablet.CurveScaledEvalMeasurable

open MeasureTheory

-- [TABLET NODE: PsiTildeMeasurable]
/-- `ψ̃_{m,Q,ε,C}` (`psiTilde`) is measurable as a function of `γ : Θ(E)`, with `Θ(E)` carrying
the evaluation `σ`-algebra of `CurveMeasurableSpace`. Needed for the same reason as
`PsiMeasurable`: `PsiVanishes` states an inequality between Bochner integrals of `psi`/`psiTilde`
against a measure on `Θ(E)`, and Lean's Bochner integral of a non-measurable (hence
non-integrable) function is definitionally `0`, so without this fact the inequality would be
satisfiable by a `ψ̃` that is not measurable at all. -/
theorem PsiTildeMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (Q : Finset E) (ε C : ℝ) :
    Measurable (fun γ : Curve E => psiTilde m Q ε C γ) := by
-- BODY
  have hlen : Measurable (fun γ : Curve E => γ.len) := CurveLenMeasurable
  have hinf : ∀ c : ℝ, Measurable
      (fun γ : Curve E => Metric.infDist (γ.toFun (c * γ.len)) (Q : Set E)) := by
    intro c
    exact (Metric.lipschitz_infDist_pt (Q : Set E)).continuous.measurable.comp
      (CurveScaledEvalMeasurable c)
  unfold psiTilde
  refine Measurable.add ((measurable_const.mul (hlen.pow_const 2)).div measurable_const) ?_
  refine Measurable.mul (by fun_prop) (Finset.measurable_sum _ (fun i _ => ?_))
  refine Measurable.min measurable_const ?_
  have h1 := hinf ((i : ℝ) / m)
  simp only [div_mul_eq_mul_div] at h1
  exact measurable_const.add (measurable_const.mul h1)
