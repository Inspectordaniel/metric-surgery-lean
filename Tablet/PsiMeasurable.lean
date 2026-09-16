import Tablet.psi
import Tablet.CurveLenMeasurable
import Tablet.CurveScaledEvalMeasurable

open MeasureTheory

-- [TABLET NODE: PsiMeasurable]
/-- `ψ_{m,Q,ε,C}` (`psi`) is measurable as a function of `γ : Θ(E)`, with `Θ(E)` carrying the
evaluation `σ`-algebra of `CurveMeasurableSpace`. Needed because `PsiVanishes` states an
inequality between Bochner integrals of `psi`/`psiTilde` against a measure on `Θ(E)`, and Lean's
Bochner integral of a non-measurable (hence non-integrable) function is definitionally `0`: without
this fact in hand, such an inequality would be satisfiable by a `ψ` that is not measurable at all,
the same shape of vacuity `psi_zero_at_m_zero` records at `m = 0`. -/
theorem PsiMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (Q : Finset E) (ε C : ℝ) :
    Measurable (fun γ : Curve E => psi m Q ε C γ) := by
-- BODY
  have hlen : Measurable (fun γ : Curve E => γ.len) := CurveLenMeasurable
  have hinf : ∀ c : ℝ, Measurable
      (fun γ : Curve E => Metric.infDist (γ.toFun (c * γ.len)) (Q : Set E)) := by
    intro c
    exact (Metric.lipschitz_infDist_pt (Q : Set E)).continuous.measurable.comp
      (CurveScaledEvalMeasurable c)
  unfold psi
  refine Measurable.add (measurable_const.mul (Finset.measurable_sum _ (fun i _ => ?_))) ?_
  · refine Measurable.min (by fun_prop) ?_
    have h1 := hinf ((i : ℝ) / m)
    have h2 := hinf (((i : ℝ) - 1) / m)
    simp only [div_mul_eq_mul_div] at h1 h2
    exact measurable_const.add (measurable_const.mul (h1.add h2))
  · exact ((measurable_const.mul (hlen.pow_const 2)).div measurable_const)
