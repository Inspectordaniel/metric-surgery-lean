import Tablet.GeodesicPairing
import Tablet.curveConcat

open Set

-- [TABLET NODE: curveSampling]
/-- The piecewise-geodesic sampling `γ^δ` of `γ` at scale `δ` (paper Def. 4.3, paper.tex line
1233): with `k = ⌈len(γ)/δ⌉` and `s_j = min(j·δ, len(γ))`, `j = 0,…,k`, the concatenation of the
geodesics `G_{γ(s_{j-1}),γ(s_j)}` for `j = 1,…,k`, built via `GeodesicPairing.G` and
`curveConcat`. -/
noncomputable def curveSampling {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) : Curve E := by
-- BODY
  have concat_end : ∀ (a b : Curve E) (h : a.toFun a.len = b.toFun 0),
      (curveConcat a b h).toFun (curveConcat a b h).len = b.toFun b.len := by
    intro a b h
    show (if a.len + b.len ≤ a.len then a.toFun (a.len + b.len)
          else b.toFun (a.len + b.len - a.len)) = b.toFun b.len
    rcases eq_or_lt_of_le b.len_nonneg with hb0 | hbpos
    · have hb0' : b.len = 0 := hb0.symm
      rw [if_pos (by linarith)]
      simpa [hb0'] using h
    · rw [if_neg (by linarith)]
      congr 1
      ring
  let s : ℕ → ℝ := fun j => min ((j : ℝ) * δ) γ.len
  let aux : (n : ℕ) → {c : Curve E // c.toFun c.len = γ.toFun (s (n + 1))} := fun n =>
    Nat.rec
      (motive := fun n => {c : Curve E // c.toFun c.len = γ.toFun (s (n + 1))})
      ⟨GP.G (γ.toFun (s 0)) (γ.toFun (s 1)), GP.end_eq _ _⟩
      (fun n ih =>
        ⟨curveConcat ih.1 (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2))))
            (by rw [ih.2]; exact (GP.start_eq _ _).symm),
          by rw [concat_end]; exact GP.end_eq _ _⟩)
      n
  exact (aux (Nat.ceil (γ.len / δ) - 1)).1
