import Tablet.Form1
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory ENNReal

-- [TABLET NODE: IsAdmissible]
/-- A finite Borel measure `μ` on `E` is admissible for a functional `T : Form1 E → ℝ` when it
dominates `T` in the sense of paper eq. (massmeasure), paper.tex line 1099 (specialized to `k = 1`):
`|T(f,π)| ≤ Lip(π) ∫_E |f| dμ` for every `1`-form `ω = (f,π)`. -/
def IsAdmissible {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (μ : Measure E) : Prop :=
-- BODY
  IsFiniteMeasure μ ∧
    ∀ ω : Form1 E, ENNReal.ofReal |T ω| ≤ (ω.piLip : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |ω.f x| ∂μ
