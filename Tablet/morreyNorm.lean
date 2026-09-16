import Tablet.Preamble

open MeasureTheory Set ENNReal

-- [TABLET NODE: morreyNorm]
/-- The Morrey norm of a Borel measure `μ` on `E` (paper eq. (2.3)). -/
noncomputable def morreyNorm {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (μ : Measure E) : ℝ≥0∞ :=
-- BODY
  ⨆ x : E, ⨆ r : ℝ, ⨆ _ : 0 < r, μ (Metric.closedBall x r) / ENNReal.ofReal r
