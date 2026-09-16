import Tablet.Preamble

open scoped NNReal

-- [TABLET NODE: ConeInterpolation]
/-- The truncated cone functions of paper Lemma A.1 (paper.tex 1634--1640 and 1668--1691). For any
finitely many (not necessarily distinct) points `e j` of a metric space `E`, any real coefficients
`c j`, any `M ≥ 0` and any `C ≥ 0`, the function `g x = τ_M (max_j (c j - C * d(x, e j)))` is
`C`-Lipschitz and bounded by `M`; and when the coefficients are *compatible* with `C`
(`|c j - c j'| ≤ C * d(e j, e j')`) and bounded by `M`, `g` interpolates them: `g (e j) = c j` for
every `j`. This is the finite McShane--Whitney Lipschitz extension. -/
theorem ConeInterpolation {E : Type*} [MetricSpace E] {l : ℕ}
    (e : Fin (l + 1) → E) (c : Fin (l + 1) → ℝ) (M : ℝ) (C : ℝ≥0) (hM : 0 ≤ M)
    (g : E → ℝ)
    (hg : ∀ x, g x = max (-M) (min M (Finset.univ.sup' Finset.univ_nonempty
            (fun j => c j - (C : ℝ) * dist x (e j))))) :
    LipschitzWith C g ∧ (∀ x, |g x| ≤ M) ∧
      ((∀ j j', |c j - c j'| ≤ (C : ℝ) * dist (e j) (e j')) → (∀ j, |c j| ≤ M) →
        ∀ j, g (e j) = c j) := by
-- BODY
  set F : E → ℝ := fun x => Finset.univ.sup' Finset.univ_nonempty
    (fun j => c j - (C : ℝ) * dist x (e j)) with hF
  have hle : ∀ (x : E) (j : Fin (l + 1)), c j - (C : ℝ) * dist x (e j) ≤ F x := by
    intro x j
    exact Finset.le_sup' (fun j => c j - (C : ℝ) * dist x (e j)) (Finset.mem_univ j)
  -- key one-sided Lipschitz bound for the cone maximum `F`
  have hkey : ∀ x y : E, F x ≤ F y + (C : ℝ) * dist x y := by
    intro x y
    rw [hF]
    refine Finset.sup'_le _ _ (fun j _ => ?_)
    have h1 : dist y (e j) ≤ dist x (e j) + dist x y := by
      rw [dist_comm x y]
      linarith [dist_triangle y x (e j)]
    have h2 : (C : ℝ) * dist y (e j) ≤ (C : ℝ) * (dist x (e j) + dist x y) :=
      mul_le_mul_of_nonneg_left h1 C.coe_nonneg
    have h3 := hle y j
    have h4 : (C : ℝ) * (dist x (e j) + dist x y)
        = (C : ℝ) * dist x (e j) + (C : ℝ) * dist x y := by ring
    linarith [h3, h2, h4.le, h4.ge]
  have hFlip : LipschitzWith C F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [Real.dist_eq, abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith [hkey x y]
    · have := hkey y x
      rw [dist_comm y x] at this
      linarith
  refine ⟨?_, ?_, ?_⟩
  · have hgf : g = fun x => max (-M) (min M (F x)) := funext hg
    rw [hgf]
    exact (hFlip.const_min M).const_max (-M)
  · intro x
    rw [hg x, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · intro hcompat hbdd j'
    have hsupeq : F (e j') = c j' := by
      apply le_antisymm
      · rw [hF]
        refine Finset.sup'_le _ _ (fun j _ => ?_)
        have hjj := hcompat j j'
        have hd : dist (e j) (e j') = dist (e j') (e j) := dist_comm _ _
        have h2 : c j - c j' ≤ |c j - c j'| := le_abs_self _
        rw [hd] at hjj
        linarith
      · have := hle (e j') j'
        simpa using this
    rw [hg (e j')]
    show max (-M) (min M (F (e j'))) = c j'
    rw [hsupeq]
    have h1 : c j' ≤ M := (abs_le.mp (hbdd j')).2
    have h2 : -M ≤ c j' := (abs_le.mp (hbdd j')).1
    rw [min_eq_right h1, max_eq_right h2]
