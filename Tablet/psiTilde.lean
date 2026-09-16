import Tablet.Curve
import Mathlib.Topology.MetricSpace.HausdorffDistance

-- [TABLET NODE: psiTilde]
/-- `ψ̃_{m,Q,ε,C}(γ)`, paper Lemma A.2 display (paper.tex line 1722), with `s_i = i·γ.len/m`. -/
noncomputable def psiTilde {E : Type*} [MetricSpace E] (m : ℕ) (Q : Finset E) (ε C : ℝ)
    (γ : Curve E) : ℝ :=
-- BODY
  2 * C ^ 2 * γ.len ^ 2 / m
    + C * γ.len / m * ∑ i ∈ Finset.Icc 1 m,
        min (2 * C) (ε + 2 * C * Metric.infDist (γ.toFun (i * γ.len / m)) (Q : Set E))
