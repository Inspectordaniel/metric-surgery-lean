import Tablet.GeodesicPairing
import Tablet.Curve
import Tablet.IsClosedCurve
import Tablet.IsPiecewiseGeodesic
import Tablet.IsDeltaEpsN
import Tablet.IsLSI
import Tablet.Form1
import Tablet.curveCurrent
import Tablet.morreyNorm
import Tablet.curveMeasure
import Tablet.smallPieceCount
import Tablet.surgeryPotential
import Tablet.CutTypeI
import Tablet.CutTypeII
import Tablet.FullBallLem
import Tablet.SurgeryStepTypeI
import Tablet.SurgeryStepTypeII

open Set ENNReal

-- [TABLET NODE: SurgeryInduction]
/-- The surgery algorithm (paper.tex lines 975-1075), formalized as a single strong induction on a
termination measure rather than as the paper's explicit while-loop with counters: for `0 < ε < 1`,
`0 < δ`, `0 < n`, and a closed piecewise-geodesic curve `γ`, there exist `N ≥ 1` and closed
piecewise-geodesic curves `(g j)_{j<N}` decomposing `γ`'s current, with the total length bounded by
`surgeryPotential ε δ n γ.len (smallPieceCount γ δ)` and each `g j`'s Morrey norm at most
`4ε⁻¹+2n+10`. This is exactly the conclusion of paper Lemma 3.1 (`surgery-lem`), specialized to
`L := γ.len`, `m := smallPieceCount γ δ`, before the algorithm has run (see `SurgeryLem`, which
supplies `smallPieceCount γ δ = 0` and recovers the paper's literal bound). -/
theorem SurgeryInduction {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (δ ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hn : 0 < n)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ surgeryPotential ε δ n γ.len (smallPieceCount γ δ) ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10)) := by
-- BODY
  classical
  -- Bookkeeping for the strong induction's envelope: the measure drop plus `0 < n` give both
  -- `B ≠ 0` and `M(η') ≤ B - 1`.
  have arith : ∀ a b m0 m1 B' : ℕ, a + m1 + n ≤ b + m0 → b + m0 ≤ B' →
      a + m1 ≤ B' - 1 ∧ 0 < B' := by
    intro a b m0 m1 B' h1 h2
    omega
  suffices H : ∀ B : ℕ, ∀ η : Curve E, IsClosedCurve η → IsPiecewiseGeodesic η →
      (n + 3) * ⌊η.len / ((1 - ε) * δ)⌋₊ + smallPieceCount η δ ≤ B →
      ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
        (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
        (∀ ω : Form1 E, curveCurrent η ω = ∑ j, curveCurrent (g j) ω) ∧
        (∑ j, (g j).len) ≤ surgeryPotential ε δ n η.len (smallPieceCount η δ) ∧
        (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * (n : ℝ) + 10)) by
    exact H _ γ hclosed hpg le_rfl
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    intro η hcl hpgη hB
    by_cases hden : IsDeltaEpsN η δ ε n
    · by_cases hlsi : IsLSI η δ ε
      · -- Case (B): the algorithm halts and returns `η` itself.
        refine ⟨1, fun _ => η, one_pos, fun _ => hcl, fun _ => hpgη, ?_, ?_, ?_⟩
        · intro ω
          simp
        · have hAnn : (0:ℝ) ≤ 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε)) := by
            have h1e : (0:ℝ) < 1 - ε := by linarith
            have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
            positivity
          have hCnn : (0:ℝ) ≤ 4 * ε⁻¹ * δ / (n : ℝ) * (smallPieceCount η δ : ℝ) := by
            have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
            positivity
          have hlen0 : (0:ℝ) ≤ η.len := η.len_nonneg
          simp only [surgeryPotential, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            one_smul]
          nlinarith [mul_nonneg hAnn hlen0]
        · intro _
          exact le_trans (FullBallLem η δ ε n hδ hε0 hε1 hden hlsi)
            (ENNReal.ofReal_le_ofReal (by linarith))
      · -- Case (C): a Type I cut.
        obtain ⟨η', d, β, hbd, _hbu, hcur, hcl', hpg', hcld, hpgd, hmor, hlen1, hlen2, hmc⟩ :=
          CutTypeI GP η δ ε n hε0 hε1 hδ hcl hpgη hden hlsi
        obtain ⟨hstep1, hstep2⟩ :=
          SurgeryStepTypeI δ ε n hε0 hε1 hδ hn η.len η'.len d.len β
            (smallPieceCount η δ) (smallPieceCount η' δ) η'.len_nonneg hbd hlen1 hlen2 hmc
        obtain ⟨hdrop, hBpos⟩ := arith _ _ _ _ _ hstep1 hB
        obtain ⟨N', h, hN'pos, hclh, hpgh, hcurh, hlenh, hmorh⟩ :=
          ih (B - 1) (by omega) η' hcl' hpg' hdrop
        refine ⟨N' + 1, Fin.cons (α := fun _ => Curve E) d h, Nat.succ_pos _, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun j => Fin.cases (motive := fun j => IsClosedCurve
            (Fin.cons (α := fun _ => Curve E) d h j))
            (by simpa using hcld) (fun i => by simpa using hclh i) j
        · exact fun j => Fin.cases (motive := fun j => IsPiecewiseGeodesic
            (Fin.cons (α := fun _ => Curve E) d h j))
            (by simpa using hpgd) (fun i => by simpa using hpgh i) j
        · intro ω
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hcur ω, hcurh ω]
          ring
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          linarith [hlenh]
        · exact fun j => Fin.cases (motive := fun j => morreyNorm
            (curveMeasure (Fin.cons (α := fun _ => Curve E) d h j)) ≤
              ENNReal.ofReal (4 * ε⁻¹ + 2 * (n : ℝ) + 10))
            (by simpa using hmor) (fun i => by simpa using hmorh i) j
    · -- Case (A): a Type II cut.
      obtain ⟨η', d, hcur, hcl', hpg', hcld, hpgd, hmor, hlen1, hlen2, hmc⟩ :=
        CutTypeII GP η δ ε n hε0 hε1 hδ hcl hpgη hden
      obtain ⟨hstep1, hstep2⟩ :=
        SurgeryStepTypeII δ ε n hε0 hε1 hδ hn η.len η'.len d.len
          (smallPieceCount η δ) (smallPieceCount η' δ) hlen1 hlen2 hmc
      obtain ⟨hdrop, hBpos⟩ := arith _ _ _ _ _ hstep1 hB
      obtain ⟨N', h, hN'pos, hclh, hpgh, hcurh, hlenh, hmorh⟩ :=
        ih (B - 1) (by omega) η' hcl' hpg' hdrop
      have hmor' : morreyNorm (curveMeasure d) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * (n : ℝ) + 10) :=
        le_trans hmor (ENNReal.ofReal_le_ofReal (by linarith))
      refine ⟨N' + 1, Fin.cons (α := fun _ => Curve E) d h, Nat.succ_pos _, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun j => Fin.cases (motive := fun j => IsClosedCurve
          (Fin.cons (α := fun _ => Curve E) d h j))
          (by simpa using hcld) (fun i => by simpa using hclh i) j
      · exact fun j => Fin.cases (motive := fun j => IsPiecewiseGeodesic
          (Fin.cons (α := fun _ => Curve E) d h j))
          (by simpa using hpgd) (fun i => by simpa using hpgh i) j
      · intro ω
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hcur ω, hcurh ω]
        ring
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        linarith [hlenh]
      · exact fun j => Fin.cases (motive := fun j => morreyNorm
          (curveMeasure (Fin.cons (α := fun _ => Curve E) d h j)) ≤
            ENNReal.ofReal (4 * ε⁻¹ + 2 * (n : ℝ) + 10))
          (by simpa using hmor') (fun i => by simpa using hmorh i) j
