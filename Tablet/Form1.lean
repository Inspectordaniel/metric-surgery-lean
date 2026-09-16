import Tablet.Preamble

open scoped NNReal

-- [TABLET NODE: Form1]
/-- A metric $1$-form $\omega = (f,\pi) \in \mathcal{D}^1(E)$: a bounded Lipschitz function `f`
paired with a Lipschitz function `pi`. The bound on `f` and the Lipschitz constants of both `f`
and `pi` are carried as explicit fields, so that `‖f‖_∞` and `Lip(pi)` are named data rather than
constructed as a suprema at each use site. -/
structure Form1 (E : Type*) [MetricSpace E] where
-- BODY
  f : E → ℝ
  fBound : ℝ≥0
  f_bounded : ∀ x : E, |f x| ≤ (fBound : ℝ)
  fLip : ℝ≥0
  f_lipschitz : LipschitzWith fLip f
  pi : E → ℝ
  piLip : ℝ≥0
  pi_lipschitz : LipschitzWith piLip pi
