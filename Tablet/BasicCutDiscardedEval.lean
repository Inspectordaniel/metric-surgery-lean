import Tablet.BasicCut
import Tablet.CurveConcatEndpoints
import Tablet.GeodesicPairing
import Tablet.IsClosedCurve
import Tablet.IsGeodesicOn
import Tablet.curveArc
import Tablet.curveConcat
import Tablet.curveRestrict
import Tablet.curveWrapRestrict

open Set

-- [TABLET NODE: BasicCutDiscardedEval]
/-- The pointwise description of the discarded output `g` of a basic cut `C(γ,t,t')`
(`BasicCut`), which is by construction the concatenation of the circular arc
`A := γ|_{[t,t']}` (`curveArc`) with the single closing geodesic edge
`C := G_{γ(t'),γ(t)}` (`GeodesicPairing`): its length is `len(A)+len(C)`, it agrees with `A`
throughout `A`'s own parameter interval `[0,len(A)]`, and on the remaining interval
`[len(A),len(g)]` it is a geodesic (`IsGeodesicOn`), being a translate of the geodesic `C`.
This is the description needed to splice a Morrey decomposition of `A` back into one of `g`:
`BasicCutLength` records `len(g)` only in the `(if t ≤ t' then t'-t else (γ.len-t)+t') + dist`
form and says nothing about the values of `g`, and `BasicCutDiscardedResolutionGeneral` records
only the *existence* of a geodesic resolution of `g`, with no identification of its pieces with
`A`'s. -/
theorem BasicCutDiscardedEval {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len)
    (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) :
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len
        = (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
          + (GP.G (γ.toFun t') (γ.toFun t)).len ∧
      (∀ v : ℝ, v ≤ (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len →
        (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.toFun v
          = (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).toFun v) ∧
      IsGeodesicOn (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2
        (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
        (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len := by
-- BODY
  -- A restriction ends where it should.
  have hrestrictEnd : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
      (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
    intro p q hp hpq hq
    show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
    rw [max_eq_right (by linarith), min_self]
    congr 1
    ring
  -- Hence the circular arc `γ|_{[a,b]}` ends at `γ(b)`, in either order of `a,b`.
  have harcEnd : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b) (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha0 hal hb0 hbl).toFun (curveArc γ hclosed a b ha0 hal hb0 hbl).len
        = γ.toFun b := by
    intro a b ha0 hal hb0 hbl
    unfold curveArc
    split_ifs with h
    · exact hrestrictEnd a b ha0 h hbl
    · unfold curveWrapRestrict
      rw [(CurveConcatEndpoints _ _ _).2]
      exact hrestrictEnd 0 b (le_refl 0) hb0 (by linarith)
  -- The generic statement about a concatenation whose second factor is a geodesic.
  have hgen : ∀ (A C : Curve E) (hm : A.toFun A.len = C.toFun 0), IsGeodesicOn C 0 C.len →
      (curveConcat A C hm).len = A.len + C.len ∧
        (∀ v : ℝ, v ≤ A.len → (curveConcat A C hm).toFun v = A.toFun v) ∧
        IsGeodesicOn (curveConcat A C hm) A.len (curveConcat A C hm).len := by
    intro A C hm hgeo
    have hlen : (curveConcat A C hm).len = A.len + C.len := rfl
    refine ⟨hlen, ?_, ?_⟩
    · intro v hv
      show (if v ≤ A.len then A.toFun v else C.toFun (v - A.len)) = A.toFun v
      rw [if_pos hv]
    · -- Beyond `A.len` the concatenation is `C` translated by `A.len`.
      have hbeyond : ∀ x : ℝ, A.len ≤ x → (curveConcat A C hm).toFun x = C.toFun (x - A.len) := by
        intro x hx
        show (if x ≤ A.len then A.toFun x else C.toFun (x - A.len)) = C.toFun (x - A.len)
        rcases eq_or_lt_of_le hx with h | h
        · rw [if_pos (by linarith)]
          rw [← h, sub_self, hm]
        · rw [if_neg (by linarith)]
      intro x hx y hy
      rw [hlen] at hx hy
      obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hy0, hy1⟩ := hy
      rw [hbeyond x hx0, hbeyond y hy0]
      rw [hgeo (x - A.len) ⟨by linarith, by linarith⟩ (y - A.len) ⟨by linarith, by linarith⟩]
      congr 1
      ring
  exact hgen (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) (GP.G (γ.toFun t') (γ.toFun t))
    (by rw [harcEnd, GP.start_eq]) (GP.isGeodesic _ _)
