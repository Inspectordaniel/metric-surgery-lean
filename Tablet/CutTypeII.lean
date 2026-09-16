import Tablet.BasicCut
import Tablet.BasicCutClosed
import Tablet.BasicCutCurrent
import Tablet.BasicCutLength
import Tablet.BasicCutDiscardedResolution
import Tablet.BasicCutResolutionAtBreakpoints
import Tablet.DeltaEpsNFailureAtBreakpoints
import Tablet.C1SmallBall
import Tablet.curveMeasure
import Tablet.curveCurrent
import Tablet.smallPieceCount

open Set ENNReal

set_option maxRecDepth 4000

-- [TABLET NODE: CutTypeII]
/-- Paper Lemma 3.9 (the Type II cut operation), existential form: for `0 < ε < 1`, `0 < δ`, and a
closed piecewise-geodesic curve `γ` that fails to be `(δ,ε,n)`-controlled, there exist closed
piecewise-geodesic curves `γ'` (kept) and `g` (discarded) with `[[γ]] = [[γ']] + [[g]]`, a Morrey
bound on `g`, length bounds on `γ'` and on the total length `γ'.len + g.len`, and a
subtraction-free small-edge-count bound `smallPieceCount γ' δ + n ≤ smallPieceCount γ δ`. -/
theorem CutTypeII {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (δ ε : ℝ) (n : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (hfail : ¬ IsDeltaEpsN γ δ ε n) :
    ∃ γ' g : Curve E,
      (∀ ω : Form1 E, curveCurrent γ ω = curveCurrent γ' ω + curveCurrent g ω) ∧
      IsClosedCurve γ' ∧ IsPiecewiseGeodesic γ' ∧
      IsClosedCurve g ∧ IsPiecewiseGeodesic g ∧
      morreyNorm (curveMeasure g) ≤ ENNReal.ofReal (2 * ((n : ℝ) + 2 * ε⁻¹ + 2)) ∧
      γ'.len ≤ γ.len ∧
      γ'.len + g.len ≤ γ.len + 4 * ε⁻¹ * δ ∧
      smallPieceCount γ' δ + n ≤ smallPieceCount γ δ := by
-- BODY
  obtain ⟨k, s, p, q, hres, hmin, hstrict, hp, hq, hne, hsmall, hbig, harc⟩ :=
    DeltaEpsNFailureAtBreakpoints γ δ ε hε hδ hclosed hpg n hfail
  obtain ⟨hmono, hs0, hsk, hgeo⟩ := hres
  have hres' : IsGeodesicResolution γ k s := ⟨hmono, hs0, hsk, hgeo⟩
  -- endpoint bounds for the cut points, from IsGeodesicResolution alone
  have hmem0 : (0 : ℕ) ∈ Set.Icc 0 k := ⟨le_rfl, Nat.zero_le _⟩
  have hmemk : k ∈ Set.Icc 0 k := ⟨Nat.zero_le _, le_rfl⟩
  have hmemp : p ∈ Set.Icc 0 k := ⟨Nat.zero_le _, hp⟩
  have hmemq : q ∈ Set.Icc 0 k := ⟨Nat.zero_le _, hq⟩
  have ht0 : 0 ≤ s p := hs0 ▸ hmono hmem0 hmemp (Nat.zero_le _)
  have htlen : s p ≤ γ.len := hsk ▸ hmono hmemp hmemk hp
  have ht'0 : 0 ≤ s q := hs0 ▸ hmono hmem0 hmemq (Nat.zero_le _)
  have ht'len : s q ≤ γ.len := hsk ▸ hmono hmemq hmemk hq
  refine ⟨(BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1,
    (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω; exact BasicCutCurrent GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len hne ω
  · exact (BasicCutClosed GP γ hclosed hpg (s p) (s q) ht0 htlen ht'0 ht'len hne).1
  · exact (BasicCutClosed GP γ hclosed hpg (s p) (s q) ht0 htlen ht'0 ht'len hne).2.1
  · exact (BasicCutClosed GP γ hclosed hpg (s p) (s q) ht0 htlen ht'0 ht'len hne).2.2.1
  · exact (BasicCutClosed GP γ hclosed hpg (s p) (s q) ht0 htlen ht'0 ht'len hne).2.2.2
  -- MORREY
  · have hpw := BasicCutDiscardedResolution GP γ hclosed k s hres' p q hp hq hne
      ht0 htlen ht'0 ht'len
    have hC1 := C1SmallBall _ _ hpw
    set card := ((Finset.Icc 1 k).filter (fun j =>
        if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card with hcarddef
    refine hC1.trans ?_
    have hreal : (2 : ℝ) * ((card : ℝ) + 1) ≤ 2 * ((n : ℝ) + 2 * ε⁻¹ + 2) := by
      have := hbig; linarith
    have hnat : ((card + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((card : ℝ) + 1) := by
      rw [show ((card : ℝ) + 1) = ((card + 1 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
    have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
    have hcast : ((2 * ((card + 1 : ℕ) : ℝ≥0∞))) = ENNReal.ofReal (2 * ((card : ℝ) + 1)) := by
      rw [hnat, htwo, ← ENNReal.ofReal_mul (by norm_num)]
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hreal
  -- LENGTHS: both come from BasicCutLength + the amended arc-length clause
  · obtain ⟨h1, h2, hdA⟩ := BasicCutLength GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len hne
    have hbr : (if s p ≤ s q then s q - s p else (γ.len - s p) + s q)
        = (if p < q then s q - s p else (γ.len - s p) + s q) := by
      by_cases hpq : p < q
      · have : s p < s q := hstrict hmemp hmemq hpq
        simp [hpq, this.le]
      · have hqp : q < p := by
          rcases Nat.lt_trichotomy p q with h | h | h
          · exact absurd h hpq
          · exact absurd (by rw [h]) hne
          · exact h
        have : s q < s p := hstrict hmemq hmemp hqp
        simp [hpq, not_le.mpr this]
    rw [hbr] at h1 h2 hdA
    rw [h1]; linarith
  · obtain ⟨h1, h2, hdA⟩ := BasicCutLength GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len hne
    have hbr : (if s p ≤ s q then s q - s p else (γ.len - s p) + s q)
        = (if p < q then s q - s p else (γ.len - s p) + s q) := by
      by_cases hpq : p < q
      · have : s p < s q := hstrict hmemp hmemq hpq
        simp [hpq, this.le]
      · have hqp : q < p := by
          rcases Nat.lt_trichotomy p q with h | h | h
          · exact absurd h hpq
          · exact absurd (by rw [h]) hne
          · exact h
        have : s q < s p := hstrict hmemq hmemp hqp
        simp [hpq, not_le.mpr this]
    rw [hbr] at h1 h2 hdA
    rw [h1, h2]; linarith
  -- SMALL COUNT
  · have hBC := BasicCutResolutionAtBreakpoints GP γ hclosed k s hres' p q hp hq hne δ
      ht0 htlen ht'0 ht'len
    rw [hsmall, hmin] at hBC
    omega
