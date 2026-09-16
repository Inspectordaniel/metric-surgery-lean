import Tablet.GeodesicPairing
import Tablet.curveArc
import Tablet.curveConcat
import Tablet.IsClosedCurve

open Set

-- [TABLET NODE: BasicCut]
/-- The basic cut `C(γ,t,t')` of a closed curve `γ` at two points `t,t' ∈ [0,len(γ)]` (paper
lines 581-583): the pair `(γ',g)` of closed curves obtained by splitting `γ` at `t,t'` and closing
each of the two resulting arcs with a single geodesic edge traversed in opposite directions.
`γ'` is the concatenation of `γ|_{[t',t]}` with the geodesic `G_{γ(t),γ(t')}`; `g` is the
concatenation of `γ|_{[t,t']}` with `G_{γ(t'),γ(t)}`, with `γ|_{[a,b]}` the circular arc
`curveArc`. -/
noncomputable def BasicCut {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t')
    (ht'len : t' ≤ γ.len) : Curve E × Curve E := by
-- BODY
  have curveArc_toFun_len : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b)
      (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha0 hal hb0 hbl).toFun (curveArc γ hclosed a b ha0 hal hb0 hbl).len
        = γ.toFun b := by
    intro a b ha0 hal hb0 hbl
    have hRestrict_len : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
        (curveRestrict γ p q hp hpq hq).len = q - p := fun _ _ _ _ _ => rfl
    have hRestrict_toFun_len : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
        (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
      intro p q hp hpq hq
      show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
      rw [max_eq_right (by linarith), min_self]
      congr 1
      ring
    unfold curveArc
    split_ifs with h
    · exact hRestrict_toFun_len a b ha0 h hbl
    · have hbt : b < a := not_le.mp h
      have hlen : (curveWrapRestrict γ a b hclosed ha0 hal hb0 hbt).len = (γ.len - a) + b := by
        show (curveRestrict γ a γ.len ha0 hal (le_refl _)).len
            + (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)).len = (γ.len - a) + b
        rw [hRestrict_len, hRestrict_len]
        ring_nf
      rw [hlen]
      show (if ((γ.len - a) + b) ≤ (curveRestrict γ a γ.len ha0 hal (le_refl _)).len
          then (curveRestrict γ a γ.len ha0 hal (le_refl _)).toFun ((γ.len - a) + b)
          else (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)).toFun
            (((γ.len - a) + b) - (curveRestrict γ a γ.len ha0 hal (le_refl _)).len))
          = γ.toFun b
      rw [hRestrict_len]
      rcases eq_or_lt_of_le hb0 with hbeq | hbpos
      · rw [if_pos (by linarith)]
        have harg : a + min (γ.len - a) (max 0 (γ.len - a + b)) = γ.len := by
          rw [max_eq_right (by linarith), min_eq_right (by linarith)]
          linarith
        show γ.toFun (a + min (γ.len - a) (max 0 (γ.len - a + b))) = γ.toFun b
        rw [harg, ← hbeq]
        exact hclosed
      · rw [if_neg (by linarith)]
        have harg : (γ.len - a) + b - (γ.len - a) = b := by ring
        rw [harg]
        have h1 := hRestrict_toFun_len 0 b (le_refl 0) hb0 (by linarith)
        simp only [hRestrict_len, sub_zero] at h1
        exact h1
  exact
    ⟨curveConcat (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen) (GP.G (γ.toFun t) (γ.toFun t'))
        (by rw [curveArc_toFun_len, GP.start_eq]),
     curveConcat (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) (GP.G (γ.toFun t') (γ.toFun t))
        (by rw [curveArc_toFun_len, GP.start_eq])⟩
