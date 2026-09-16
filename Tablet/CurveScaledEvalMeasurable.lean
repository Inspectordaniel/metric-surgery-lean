import Tablet.CurveEvalJointMeasurable
import Tablet.CurveLenMeasurable

-- [TABLET NODE: CurveScaledEvalMeasurable]
theorem CurveScaledEvalMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) : Measurable (fun γ : Curve E => γ.toFun (c * γ.len)) := by
-- BODY
  exact CurveEvalJointMeasurable.comp
    ((measurable_const.mul CurveLenMeasurable).prodMk measurable_id)
