import Tablet.IsAdmissible

open MeasureTheory ENNReal

-- [TABLET NODE: massOfFunctional]
/-- The mass `𝕄(T)` of a functional `T : Form1 E → ℝ` (paper.tex line 1100), defined as the
infimum of the total mass `μ(E)` over admissible measures `μ` (\noderef{IsAdmissible}), rather than
via the minimum admissible measure (whose existence is Ambrosio–Kirchheim's theorem, and which this
tablet does not construct). When some admissible measure exists this agrees with the paper's
`μ_T(E)` for the (existing) minimal admissible measure `μ_T`, since the infimum of total masses over
the admissible class is achieved exactly at any pointwise-minimal element of that class. -/
noncomputable def massOfFunctional {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) : ℝ≥0∞ :=
-- BODY
  ⨅ μ : { μ : Measure E // IsAdmissible T μ }, (μ.1 Set.univ)
