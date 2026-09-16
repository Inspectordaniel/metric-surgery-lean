import Tablet.CurveMeasurableSpace
import Tablet.CurveLipschitz
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

open MeasureTheory

-- [TABLET NODE: CurveEvalJointMeasurable]
theorem CurveEvalJointMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (Function.uncurry (fun (t : ℝ) (γ : Curve E) => γ.toFun t)) := by
-- BODY
  have heval : Measurable (fun γ : Curve E => (γ.len, γ.toFun)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hpt : ∀ t : ℝ, Measurable (fun γ : Curve E => γ.toFun t) :=
    fun t => ((measurable_pi_apply t).comp measurable_snd).comp heval
  exact measurable_uncurry_of_continuous_of_measurable
    (fun γ => (CurveLipschitz γ).continuous) hpt
