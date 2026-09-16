import Tablet.GeodesicPairing
import Tablet.Curve
import Tablet.IsClosedCurve
import Tablet.IsPiecewiseGeodesic
import Tablet.Form1
import Tablet.curveCurrent
import Tablet.morreyNorm
import Tablet.curveMeasure
import Tablet.surgeryPotential
import Tablet.smallPieceCount
import Tablet.InitialDeltaExists
import Tablet.SurgeryInduction

open Set ENNReal

-- [TABLET NODE: SurgeryLem]
/-- Paper Lemma 3.1 (`surgery-lem`, paper.tex lines 597-621), with the paper's literal length
factor `(1 + 2ε/(1-ε) + 12ε⁻¹/(n(1-ε))) * γ.len` and Morrey bound `4ε⁻¹+2n+10`, recovered from
`SurgeryInduction` (the algorithm's conclusion before it has run, at a starting scale `δ` supplied
by `InitialDeltaExists` with `smallPieceCount γ δ = 0`), plus a direct degenerate-length argument
when `γ.len = 0` (where `InitialDeltaExists` does not apply). `δ` does not appear in the
statement: it is existentially consumed inside the proof, exactly as in the paper. -/
theorem SurgeryLem {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hn : 0 < n)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10)) := by
-- BODY
  rcases eq_or_lt_of_le γ.len_nonneg with hlen0 | hlen
  · refine ⟨1, fun _ => γ, one_pos, fun _ => hclosed, fun _ => hpg, ?_, ?_, ?_⟩
    · intro ω
      simp
    · simp only [Fin.sum_univ_one]
      rw [← hlen0]
      simp
    · intro _
      have hicc : Set.Icc (0:ℝ) γ.len = ({0} : Set ℝ) := by
        rw [← hlen0]; simp
      have hzero : (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) γ.len)) = 0 := by
        rw [hicc]
        exact MeasureTheory.Measure.restrict_eq_zero.mpr Real.volume_singleton
      have hmeas : curveMeasure γ = 0 := by
        unfold curveMeasure
        rw [hzero, MeasureTheory.Measure.map_zero]
      rw [hmeas]
      have hmz : morreyNorm (0 : MeasureTheory.Measure E) = 0 := by
        unfold morreyNorm
        simp
      rw [hmz]
      exact zero_le
  · obtain ⟨δ, hdpos, hspc, -⟩ := InitialDeltaExists γ hpg hclosed hlen ε hε0
    obtain ⟨N, g, hN, hcl, hpgj, hcur, hlen', hmor⟩ :=
      SurgeryInduction GP γ δ ε n hε0 hε1 hdpos hn hclosed hpg
    refine ⟨N, g, hN, hcl, hpgj, hcur, ?_, hmor⟩
    rw [hspc] at hlen'
    simpa [surgeryPotential] using hlen'
