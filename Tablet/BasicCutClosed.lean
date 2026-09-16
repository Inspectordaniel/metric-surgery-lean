import Tablet.BasicCut
import Tablet.curveArc
import Tablet.ArcGeodesicResolution
import Tablet.BasicCutDiscardedResolutionGeneral
import Tablet.CurveConcatEndpoints
import Tablet.IsPiecewiseGeodesic
import Tablet.IsGeodesicResolution
import Tablet.IsGeodesicOn
import Tablet.curveRestrict
import Tablet.curveWrapRestrict
import Tablet.curveConcat
import Tablet.GeodesicPairing
import Tablet.IsClosedCurve

open Set

-- [TABLET NODE: BasicCutClosed]
/-- Both outputs of `BasicCut γ t t'` (for `t ≠ t'`) are closed, piecewise-geodesic curves,
provided `γ` itself is closed and piecewise-geodesic (paper.tex lines 581-583). -/
theorem BasicCutClosed {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) (t t' : ℝ)
    (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) (hne : t ≠ t') :
    IsClosedCurve (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ∧
      IsPiecewiseGeodesic (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ∧
      IsClosedCurve (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 ∧
      IsPiecewiseGeodesic (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 := by
-- BODY
  classical
  obtain ⟨k, s, hres⟩ := hpg
  -- A restriction starts where it should.
  have hrestrictStart : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
      (curveRestrict γ p q hp hpq hq).toFun 0 = γ.toFun p := by
    intro p q hp hpq hq
    show γ.toFun (p + min (q - p) (max 0 0)) = γ.toFun p
    rw [max_self, min_eq_right (by linarith), add_zero]
  -- A restriction ends where it should.
  have hrestrictEnd : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
      (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
    intro p q hp hpq hq
    show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
    rw [max_eq_right (by linarith), min_self]
    congr 1
    ring
  -- Hence the circular arc `γ|_{[a,b]}` starts at `γ(a)` (Part 1's endpoint bookkeeping): in the
  -- ordinary case it is the plain restriction, in the wrap case it is a concatenation whose first
  -- factor is the restriction `γ|_{[a,len(γ)]}`.
  have harcStart : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b) (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha0 hal hb0 hbl).toFun 0 = γ.toFun a := by
    intro a b ha0 hal hb0 hbl
    unfold curveArc
    split_ifs with h
    · exact hrestrictStart a b ha0 h hbl
    · show (curveConcat (curveRestrict γ a γ.len ha0 hal (le_refl _))
        (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)) _).toFun 0 = γ.toFun a
      rw [(CurveConcatEndpoints _ _ _).1]
      exact hrestrictStart a γ.len ha0 hal (le_refl _)
  -- ... and ends at `γ(b)`, symmetrically.
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
  -- The discarded output of a basic cut at *any* pair of distinct cut points is closed and
  -- piecewise geodesic.  Both conclusions of the lemma are instances of this, because the kept
  -- output at `(t,t')` is literally the discarded output at `(t',t)`.
  have main : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b) (hbl : b ≤ γ.len),
      a ≠ b →
      IsClosedCurve (BasicCut GP γ hclosed a b ha0 hal hb0 hbl).2 ∧
        IsPiecewiseGeodesic (BasicCut GP γ hclosed a b ha0 hal hb0 hbl).2 := by
    intro a b ha0 hal hb0 hbl hab
    constructor
    · -- Part 1: closedness.  `A * G_{γ(b),γ(a)}` starts at `A(0)` and ends at `γ(a)`.
      have hgen : ∀ (A : Curve E) (x y : E) (hm : A.toFun A.len = (GP.G x y).toFun 0),
          A.toFun 0 = y → IsClosedCurve (curveConcat A (GP.G x y) hm) := by
        intro A x y hm h0
        obtain ⟨e0, elen⟩ := CurveConcatEndpoints A (GP.G x y) hm
        show (curveConcat A (GP.G x y) hm).toFun (curveConcat A (GP.G x y) hm).len
            = (curveConcat A (GP.G x y) hm).toFun 0
        rw [e0, elen, h0, GP.end_eq]
      exact hgen (curveArc γ hclosed a b ha0 hal hb0 hbl) (γ.toFun b) (γ.toFun a)
        ((harcEnd a b ha0 hal hb0 hbl).trans (GP.start_eq _ _).symm)
        (harcStart a b ha0 hal hb0 hbl)
    · -- Part 2: piecewise-geodesic-ness, from the arc's own resolution plus the closing edge.
      obtain ⟨kA, sA, _, hresA, _, _⟩ :=
        ArcGeodesicResolution γ hclosed k s hres a b ha0 hal hb0 hbl
      exact ⟨kA + 1, BasicCutDiscardedResolutionGeneral GP γ hclosed a b ha0 hal hb0 hbl hab
        kA sA hresA⟩
  have hswap : (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1
      = (BasicCut GP γ hclosed t' t ht'0 ht'len ht0 htlen).2 := rfl
  obtain ⟨c1, p1⟩ := main t' t ht'0 ht'len ht0 htlen (Ne.symm hne)
  obtain ⟨c2, p2⟩ := main t t' ht0 htlen ht'0 ht'len hne
  rw [hswap]
  exact ⟨c1, p1, c2, p2⟩
