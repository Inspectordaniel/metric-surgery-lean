import Tablet.curveArc

open Set

-- [TABLET NODE: CurveArcEval]
/-- The arc-to-ambient evaluation dictionary for the counter-clockwise circular arc
`A := γ|_{[t,t']}` (`curveArc`) of a closed curve `γ`, uniform in the order of `t,t'`. Writing
`ℓ(a,b) := b - a` when `a ≤ b` and `ℓ(a,b) := (γ.len - a) + b` otherwise for the ccw arc length
from `a` to `b`, it says: the arc's length is `ℓ(t,t')`, and there is a reparametrization
`σ : ℝ → ℝ` of the arc's own parameter interval `[0,A.len]` back into `γ`'s parameter interval
`[0,γ.len]` which starts at `t`, satisfies `A p = γ (σ p)` throughout, ends at `t'` *as a point of
`E`* (`γ (σ A.len) = γ t'`; in the wrap case with `t' = 0` one has `σ A.len = γ.len ≠ t'`, and only
closedness of `γ` rescues the identity), and is an isometry for ccw arc length:
`ℓ(σ p, σ p') = p' - p` whenever `p ≤ p'` in `[0,A.len]`. -/
theorem CurveArcEval {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) :
    (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len
        = (if t ≤ t' then t' - t else (γ.len - t) + t') ∧
      ∃ σ : ℝ → ℝ,
        σ 0 = t ∧
        γ.toFun (σ (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len) = γ.toFun t' ∧
        (∀ p ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len,
          σ p ∈ Set.Icc (0 : ℝ) γ.len ∧
            (curveArc γ hcl t t' ht0 htl ht'0 ht'l).toFun p = γ.toFun (σ p)) ∧
        (∀ p ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len,
          ∀ p' ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len, p ≤ p' →
            (if σ p ≤ σ p' then σ p' - σ p else (γ.len - σ p) + σ p') = p' - p) := by
-- BODY
  have hcl' : γ.toFun γ.len = γ.toFun 0 := hcl
  by_cases h : t ≤ t'
  · -- Ordinary case: the arc is the plain restriction `γ|_{[t,t']}`.
    have hA : curveArc γ hcl t t' ht0 htl ht'0 ht'l = curveRestrict γ t t' ht0 h ht'l := by
      unfold curveArc; exact dif_pos h
    rw [hA]
    have hRlen : (curveRestrict γ t t' ht0 h ht'l).len = t' - t := rfl
    have hRfun : ∀ p : ℝ, (curveRestrict γ t t' ht0 h ht'l).toFun p
        = γ.toFun (t + min (t' - t) (max 0 p)) := fun _ => rfl
    refine ⟨by rw [hRlen, if_pos h], fun p => t + p, by ring, ?_, ?_, ?_⟩
    · rw [hRlen]
      show γ.toFun (t + (t' - t)) = γ.toFun t'
      congr 1; ring
    · intro p hp
      obtain ⟨hp0, hp1⟩ := hp
      rw [hRlen] at hp1
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rw [hRfun p, max_eq_right hp0, min_eq_right hp1]
    · intro p _ p' _ hpp
      rw [if_pos (by linarith : t + p ≤ t + p')]
      ring
  · -- Wrap case: the arc is `γ|_{[t,γ.len]}` followed by `γ|_{[0,t']}`.
    have hlt : t' < t := not_le.mp h
    have hA : curveArc γ hcl t t' ht0 htl ht'0 ht'l
        = curveWrapRestrict γ t t' hcl ht0 htl ht'0 hlt := by
      unfold curveArc; exact dif_neg h
    rw [hA]
    have hR0 : (0 : ℝ) ≤ γ.len - t := by linarith
    have hWlen : (curveWrapRestrict γ t t' hcl ht0 htl ht'0 hlt).len = (γ.len - t) + t' := by
      show (γ.len - t) + (t' - 0) = (γ.len - t) + t'
      ring
    have hWfun : ∀ p : ℝ, (curveWrapRestrict γ t t' hcl ht0 htl ht'0 hlt).toFun p
        = if p ≤ γ.len - t then γ.toFun (t + min (γ.len - t) (max 0 p))
          else γ.toFun (0 + min (t' - 0) (max 0 (p - (γ.len - t)))) := fun _ => rfl
    refine ⟨by rw [hWlen, if_neg h],
      fun p => if p ≤ γ.len - t then t + p else p - (γ.len - t), ?_, ?_, ?_, ?_⟩
    · show (if (0 : ℝ) ≤ γ.len - t then t + (0 : ℝ) else (0 : ℝ) - (γ.len - t)) = t
      rw [if_pos hR0]; ring
    · rw [hWlen]
      rcases eq_or_lt_of_le ht'0 with he | hpos
      · -- `t' = 0`: the arc ends at parameter `γ.len`, and closedness identifies it with `γ(0)`.
        show γ.toFun (if (γ.len - t) + t' ≤ γ.len - t then t + ((γ.len - t) + t')
          else ((γ.len - t) + t') - (γ.len - t)) = γ.toFun t'
        rw [if_pos (by linarith)]
        have hgl : t + ((γ.len - t) + t') = γ.len := by linarith
        rw [hgl, hcl']
        exact congr_arg γ.toFun he
      · show γ.toFun (if (γ.len - t) + t' ≤ γ.len - t then t + ((γ.len - t) + t')
          else ((γ.len - t) + t') - (γ.len - t)) = γ.toFun t'
        rw [if_neg (by linarith)]
        congr 1; ring
    · intro p hp
      obtain ⟨hp0, hp1⟩ := hp
      rw [hWlen] at hp1
      by_cases hpR : p ≤ γ.len - t
      · refine ⟨?_, ?_⟩
        · show (if p ≤ γ.len - t then t + p else p - (γ.len - t)) ∈ Set.Icc (0 : ℝ) γ.len
          rw [if_pos hpR]
          exact ⟨by linarith, by linarith⟩
        · rw [hWfun p]
          simp only [if_pos hpR]
          rw [max_eq_right hp0, min_eq_right hpR]
      · have hpR' : γ.len - t < p := not_le.mp hpR
        refine ⟨?_, ?_⟩
        · show (if p ≤ γ.len - t then t + p else p - (γ.len - t)) ∈ Set.Icc (0 : ℝ) γ.len
          rw [if_neg hpR]
          exact ⟨by linarith, by linarith⟩
        · rw [hWfun p]
          simp only [if_neg hpR]
          rw [sub_zero, max_eq_right (by linarith : (0 : ℝ) ≤ p - (γ.len - t)),
            min_eq_right (by linarith : p - (γ.len - t) ≤ t'), zero_add]
    · intro p hp p' hp' hpp
      obtain ⟨hp0, hp1⟩ := hp
      obtain ⟨hp'0, hp'1⟩ := hp'
      rw [hWlen] at hp1 hp'1
      by_cases hpR : p ≤ γ.len - t
      · by_cases hp'R : p' ≤ γ.len - t
        · simp only [if_pos hpR, if_pos hp'R]
          rw [if_pos (by linarith : t + p ≤ t + p')]
          ring
        · simp only [if_pos hpR, if_neg hp'R]
          rw [if_neg (by
            refine not_le.mpr ?_
            linarith : ¬ (t + p ≤ p' - (γ.len - t)))]
          ring
      · have hpR' : γ.len - t < p := not_le.mp hpR
        by_cases hp'R : p' ≤ γ.len - t
        · exact absurd hp'R (by exact not_le.mpr (by linarith))
        · simp only [if_neg hpR, if_neg hp'R]
          rw [if_pos (by linarith : p - (γ.len - t) ≤ p' - (γ.len - t))]
          ring
