import Tablet.curveConcat

open Set

-- [TABLET NODE: CurveConcatEndpoints]
/-- The concatenation `γ₁ * γ₂` starts where `γ₁` starts and ends where `γ₂` ends (currently
re-derived inline both inside `curveSampling`'s own definition and inside `SamplingEndpoints`;
`ClosingUp` needs it a third time, to show that a sampled-and-closed-off curve is closed). -/
theorem CurveConcatEndpoints {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) :
    (curveConcat γ₁ γ₂ h).toFun 0 = γ₁.toFun 0 ∧
      (curveConcat γ₁ γ₂ h).toFun (curveConcat γ₁ γ₂ h).len = γ₂.toFun γ₂.len := by
-- BODY
  constructor
  · show (if (0:ℝ) ≤ γ₁.len then γ₁.toFun 0 else γ₂.toFun (0 - γ₁.len)) = γ₁.toFun 0
    rw [if_pos γ₁.len_nonneg]
  · show (if γ₁.len + γ₂.len ≤ γ₁.len then γ₁.toFun (γ₁.len + γ₂.len)
          else γ₂.toFun (γ₁.len + γ₂.len - γ₁.len)) = γ₂.toFun γ₂.len
    rcases eq_or_lt_of_le γ₂.len_nonneg with hb0 | hbpos
    · rw [if_pos (by linarith)]
      simpa [← hb0] using h
    · rw [if_neg (by linarith)]
      congr 1
      ring
