import Tablet.Preamble

-- [TABLET NODE: surgeryPotential]
/-- The surgery algorithm's termination potential (paper Lemma 3.1's clause (2), paper.tex line
612): `Φ(ε,δ,n,L,m) = A(ε,n) * L + C(ε,δ,n) * m` where `A(ε,n) = 1 + 2ε/(1-ε) + 12ε⁻¹/(n(1-ε))`
is the length-growth factor and `C(ε,δ,n) = 4ε⁻¹δ/n` is the per-small-edge length cost. `L` stands
for a curve's length and `m` for its small-edge count (`smallPieceCount`). -/
noncomputable def surgeryPotential (ε δ : ℝ) (n : ℕ) (L : ℝ) (m : ℕ) : ℝ :=
-- BODY
  (1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * L + (4 * ε⁻¹ * δ / (n : ℝ)) * m
