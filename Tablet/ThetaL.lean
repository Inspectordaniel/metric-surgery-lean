import Tablet.massOfFunctional
import Tablet.curveCurrent

open ENNReal

-- [TABLET NODE: ThetaL]
/-- The set `Θ_l(E)` of curves whose current has mass exactly `l` (paper.tex line 1178). -/
def ThetaL {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] (l : ℕ) :
    Set (Curve E) :=
-- BODY
  { γ | massOfFunctional (curveCurrent γ) = (l : ℝ≥0∞) }
