import Tablet.psiTilde

-- [TABLET NODE: PsiTildeUniformBound]
/-- The a priori two-sided bound on `ψ̃_{m,Q,ε,C}` used for integrability, companion to
`\noderef{PsiUniformBound}`: for `m ≥ 1`, `ε ≥ 0` and `C ≥ 0`, the quantity
`ψ̃_{m,Q,ε,C}(γ)` of `\noderef{psiTilde}` is nonnegative and bounded above by the same
expression `2C²·length(γ) + 2C²·length(γ)²/m`, depending only on `m`, `C` and `length(γ)`.
The upper bound comes from discarding the second argument of each of the `m` minima in
`\noderef{psiTilde}`'s defining sum, so no `infDist` estimate enters at all. -/
theorem PsiTildeUniformBound {E : Type*} [MetricSpace E] (m : ℕ) (hm : 0 < m) (Q : Finset E)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (γ : Curve E) :
    0 ≤ psiTilde m Q ε C γ ∧
      psiTilde m Q ε C γ ≤ 2 * C ^ 2 * γ.len + 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by
-- BODY
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hgl : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hcoef : (0:ℝ) ≤ C * γ.len / (m : ℝ) := by positivity
  have htail : (0:ℝ) ≤ 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by positivity
  have hsumnn : (0:ℝ) ≤ ∑ i ∈ Finset.Icc 1 m,
      min (2 * C)
        (ε + 2 * C * Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E)) := by
    refine Finset.sum_nonneg ?_
    intro i _
    refine le_min (by positivity) ?_
    have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E) :=
      Metric.infDist_nonneg
    nlinarith
  unfold psiTilde
  refine ⟨add_nonneg htail (mul_nonneg hcoef hsumnn), ?_⟩
  have hsum := Finset.sum_le_sum (f := fun i : ℕ =>
      min (2 * C)
        (ε + 2 * C * Metric.infDist (γ.toFun ((i : ℝ) * γ.len / (m : ℝ))) (Q : Set E)))
    (g := fun _ : ℕ => 2 * C) (s := Finset.Icc 1 m) (fun i _ => min_le_left _ _)
  rw [Finset.sum_const, Nat.card_Icc] at hsum
  simp only [nsmul_eq_mul, Nat.add_sub_cancel] at hsum
  have hNc : C * γ.len / (m : ℝ) * ((m : ℝ) * (2 * C)) = 2 * C ^ 2 * γ.len := by field_simp
  have key := mul_le_mul_of_nonneg_left hsum hcoef
  rw [hNc] at key
  linarith
