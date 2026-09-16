import Tablet.Curve
import Tablet.CurveLipschitz
import Tablet.curveRestrictTot

-- [TABLET NODE: CurveMeasurableSpace]
/-- The evaluation `σ`-algebra on `Curve E`: the coarsest `MeasurableSpace` structure making the
evaluation map `γ ↦ (γ.len, γ.toFun)` measurable, i.e. the `comap` of the product `MeasurableSpace`
on `ℝ × (ℝ → E)` along that map. This is the structure with respect to which every measure-theoretic
statement about curves in this tablet (the Paolini–Stepanov family, its marginals, mass) is stated. -/
instance CurveMeasurableSpace {E : Type*} [MetricSpace E] [MeasurableSpace E] :
    MeasurableSpace (Curve E) :=
-- BODY
  MeasurableSpace.comap (fun γ => (γ.len, γ.toFun)) inferInstance
