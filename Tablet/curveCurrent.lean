import Tablet.Curve
import Tablet.Form1

-- [TABLET NODE: curveCurrent]
/-- The current $[[\gamma]](\omega)$ of a curve $\gamma$ against a $1$-form $\omega = (f,\pi)$
(paper eq. (4.3)): the Lebesgue integral $\int_0^{\length(\gamma)} f(\gamma(t)) \cdot
\deriv(\pi \circ \gamma)(t)\,dt$, which computes the paper's Riemann-Stieltjes integral because
$\pi \circ \gamma$ is globally Lipschitz, hence absolutely continuous. -/
noncomputable def curveCurrent {E : Type*} [MetricSpace E] (γ : Curve E) (ω : Form1 E) : ℝ :=
-- BODY
  ∫ t in (0:ℝ)..γ.len, ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t
