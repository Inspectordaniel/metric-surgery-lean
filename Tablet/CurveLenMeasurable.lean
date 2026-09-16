import Tablet.CurveMeasurableSpace

-- [TABLET NODE: CurveLenMeasurable]
theorem CurveLenMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] :
    Measurable (fun γ : Curve E => γ.len) := by
-- BODY
  have heval : Measurable (fun γ : Curve E => (γ.len, γ.toFun)) :=
    measurable_iff_comap_le.mpr le_rfl
  exact measurable_fst.comp heval
