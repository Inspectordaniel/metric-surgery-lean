import Tablet.massOfFunctional

open MeasureTheory ENNReal Filter Topology
open scoped NNReal

-- [TABLET NODE: MetricCurrent1]
/-- A metric $1$-current on `E` (Ambrosio–Kirchheim `Def. 3.1`, specialized to `k = 1`,
`\mathcal{M}_1(E)`, paper.tex line 1101): a functional `toFun : Form1 E → ℝ` that is bilinear in
`(f,π)` (`add_f`/`smul_f`/`add_pi`/`smul_pi`), continuous with respect to pointwise convergence of
`π` with uniformly bounded Lipschitz constants (`continuous_pi`, paper.tex line 1393), local
(`locality`), and of finite mass (`finiteMass`, the specialization of the mass-measure inequality
paper.tex line 1099 to a genuine current, `massOfFunctional toFun ≠ ⊤`). Continuity with respect to
pointwise convergence of `f` is deliberately *not* an axiom here: paper.tex line 1393 derives it
from `finiteMass` together with Lebesgue's dominated convergence theorem, so axiomatizing it would
strengthen the definition beyond what the paper justifies. -/
structure MetricCurrent1 (E : Type*) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] where
-- BODY
  toFun : Form1 E → ℝ
  add_f : ∀ ω1 ω2 ω12 : Form1 E, ω1.pi = ω2.pi → ω1.pi = ω12.pi →
      (∀ x, ω12.f x = ω1.f x + ω2.f x) → toFun ω12 = toFun ω1 + toFun ω2
  smul_f : ∀ (ω ωc : Form1 E) (c : ℝ), ωc.pi = ω.pi →
      (∀ x, ωc.f x = c * ω.f x) → toFun ωc = c * toFun ω
  add_pi : ∀ ω1 ω2 ω12 : Form1 E, ω1.f = ω2.f → ω1.f = ω12.f →
      (∀ x, ω12.pi x = ω1.pi x + ω2.pi x) → toFun ω12 = toFun ω1 + toFun ω2
  smul_pi : ∀ (ω ωc : Form1 E) (c : ℝ), ωc.f = ω.f →
      (∀ x, ωc.pi x = c * ω.pi x) → toFun ωc = c * toFun ω
  continuous_pi : ∀ (f : E → ℝ) (bF : ℝ≥0) (hbF : ∀ x, |f x| ≤ (bF : ℝ)) (LF : ℝ≥0)
      (hLF : LipschitzWith LF f) (π : E → ℝ) (Lπ : ℝ≥0) (hLπ : LipschitzWith Lπ π)
      (πs : ℕ → E → ℝ) (Ls : ℕ → ℝ≥0) (hLs : ∀ n, LipschitzWith (Ls n) (πs n))
      (L0 : ℝ≥0) (hbound : ∀ n, Ls n ≤ L0)
      (hconv : ∀ x, Tendsto (fun n => πs n x) atTop (nhds (π x))),
      Tendsto (fun n => toFun ⟨f, bF, hbF, LF, hLF, πs n, Ls n, hLs n⟩) atTop
        (nhds (toFun ⟨f, bF, hbF, LF, hLF, π, Lπ, hLπ⟩))
  locality : ∀ ω : Form1 E,
      (∃ U : Set E, IsOpen U ∧ {x | ω.f x ≠ 0} ⊆ U ∧ ∃ c : ℝ, ∀ x ∈ U, ω.pi x = c) →
      toFun ω = 0
  finiteMass : massOfFunctional toFun ≠ (⊤ : ℝ≥0∞)
