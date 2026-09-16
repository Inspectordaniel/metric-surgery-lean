import Tablet.Form1

open scoped NNReal

-- [TABLET NODE: BoundaryZero]
/-- The boundary vanishing condition for a functional `T : Form1 E → ℝ` (paper.tex lines
1112–1120): `∂T = 0`, i.e. `T(dω) = 0` for every `ω ∈ \mathcal{D}^0(E)`, specialized to `k = 1` so
that `dω = (1,f)` for `ω = f` ranging over bounded Lipschitz functions. Built from `Form1` by
pairing the constant function `1` (bounded by `1`, `0`-Lipschitz) with `f`. -/
def BoundaryZero {E : Type*} [MetricSpace E] (T : Form1 E → ℝ) : Prop :=
-- BODY
  ∀ (f : E → ℝ) (b : ℝ≥0) (_hb : ∀ x, |f x| ≤ (b : ℝ)) (L : ℝ≥0) (hL : LipschitzWith L f),
    T ⟨fun _ => (1 : ℝ), 1, fun x => by simp, 0,
        by simp [LipschitzWith.const (α := E) (1 : ℝ)], f, L, hL⟩ = 0
