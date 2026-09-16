import Tablet.Curve
import Mathlib.Topology.MetricSpace.HausdorffDistance

-- [TABLET NODE: psi]
/-- `ψ_{m,Q,ε,C}(γ)`, paper Lemma A.2 display (paper.tex line 1718), with `s_i = i·γ.len/m`. -/
noncomputable def psi {E : Type*} [MetricSpace E] (m : ℕ) (Q : Finset E) (ε C : ℝ)
    (γ : Curve E) : ℝ :=
-- BODY
  C * (∑ i ∈ Finset.Icc 1 m,
        min (2 * C * γ.len / m)
          (2 * ε + 2 * C * (Metric.infDist (γ.toFun (i * γ.len / m)) (Q : Set E)
                          + Metric.infDist (γ.toFun ((i - 1) * γ.len / m)) (Q : Set E))))
    + 2 * C ^ 2 * γ.len ^ 2 / m
