import Tablet.psi

-- [TABLET NODE: PsiUniformBound]
/-- The a priori two-sided bound on `ψ_{m,Q,ε,C}` used for integrability: for `m ≥ 1`,
`ε ≥ 0` and `C ≥ 0`, the quantity `ψ_{m,Q,ε,C}(γ)` of `\noderef{psi}` is nonnegative and
bounded above by `2C²·length(γ) + 2C²·length(γ)²/m`, a quantity depending only on `m`, `C`
and `length(γ)` — in particular not on `Q`, not on `ε`, and not on the curve `γ` beyond its
length. The upper bound comes from discarding the second argument of each of the `m` minima in
`\noderef{psi}`'s defining sum, so no `infDist` estimate enters at all. -/
theorem PsiUniformBound {E : Type*} [MetricSpace E] (m : ℕ) (hm : 0 < m) (Q : Finset E)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (γ : Curve E) :
    0 ≤ psi m Q ε C γ ∧
      psi m Q ε C γ ≤ 2 * C ^ 2 * γ.len + 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by
-- BODY
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hgl : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hfst : (0:ℝ) ≤ 2 * C * γ.len / (m : ℝ) :=
    div_nonneg (by nlinarith) hmR.le
  have htail : (0:ℝ) ≤ 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by positivity
  unfold psi
  constructor
  · refine le_add_of_nonneg_of_le (mul_nonneg hC (Finset.sum_nonneg ?_)) htail
    intro i _
    refine le_min hfst ?_
    have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E) :=
      Metric.infDist_nonneg
    have h2 : (0:ℝ) ≤ Metric.infDist (γ.toFun (((i : ℝ) - 1) * γ.len / (m : ℝ))) (Q : Set E) :=
      Metric.infDist_nonneg
    nlinarith
  · have hsum := Finset.sum_le_sum (f := fun i : ℕ =>
      min (2 * C * γ.len / (m : ℝ))
        (2 * ε + 2 * C * (Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E)
          + Metric.infDist (γ.toFun (((i : ℝ) - 1) * γ.len / (m : ℝ))) (Q : Set E))))
      (g := fun _ : ℕ => 2 * C * γ.len / (m : ℝ)) (s := Finset.Icc 1 m)
      (fun i _ => min_le_left _ _)
    rw [Finset.sum_const, Nat.card_Icc] at hsum
    simp only [nsmul_eq_mul, Nat.add_sub_cancel] at hsum
    have hNc : (m : ℝ) * (2 * C * γ.len / (m : ℝ)) = 2 * C * γ.len := by field_simp
    rw [hNc] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hsum hC]
