import Tablet.ThetaL
import Tablet.curveRestrictTot
import Tablet.CurveMeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ENNReal

-- [TABLET NODE: PSFamily]
/-- The Paolini–Stepanov by-product family for a functional `T : Form1 E → ℝ`: a sequence of
finite Borel measures `η_l` on `Θ(E)` (`l ∈ ℕ`), one for each integer length, together with the
identities eq. (4.6) (`weakLength`), eq. (4.8) (`lengthExactly`), eq. (4.7) (`massMarginal`), and
Lemma A.5 (`marginal`) that Paolini–Stepanov's construction produces as by-products
(paper.tex lines 1178–1216). -/
structure PSFamily {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) where
-- BODY
  /-- `η_l`, a Borel measure on `Θ(E)` for each `l ∈ ℕ`. -/
  eta : ℕ → Measure (Curve E)
  /-- Each `η_l` is a finite measure. -/
  finite : ∀ l : ℕ, IsFiniteMeasure (eta l)
  /-- `η_l` is supported on `Θ_l(E)` for `l ≥ 1`. -/
  supported : ∀ l : ℕ, 1 ≤ l → eta l ((ThetaL l : Set (Curve E))ᶜ) = 0
  /-- Eq.~(4.8): `𝕄([[γ]]) = length(γ) = l` for `η_l`-a.e.\ `γ`, `l ≥ 1`. -/
  lengthExactly : ∀ l : ℕ, 1 ≤ l → ∀ᵐ γ ∂(eta l), γ.len = (l : ℝ)
  /-- Eq.~(4.6): `T(ω) = (1/l) ∫ [[γ]](ω) dη_l(γ)` for every `1`-form `ω`, `l ≥ 1`. -/
  weakLength : ∀ l : ℕ, 1 ≤ l → ∀ ω : Form1 E,
    T ω = (l : ℝ)⁻¹ * ∫ γ, curveCurrent γ ω ∂(eta l)
  /-- The mass measure `μ_T` of `T` (paper.tex line 1100), carried as data alongside its
  characterization via `η_l`'s beginning/ending marginals. -/
  massMeasure : Measure E
  massMeasure_finite : IsFiniteMeasure massMeasure
  /-- Eq.~(4.7): for every nonnegative measurable `φ : E → ℝ≥0∞` and `l ≥ 1`, `∫ φ dμ_T` equals
  both the `η_l`-average of `φ` at the curve's start and at its end. -/
  massMarginal : ∀ l : ℕ, 1 ≤ l → ∀ φ : E → ℝ≥0∞, Measurable φ →
    (∫⁻ x, φ x ∂massMeasure = ∫⁻ γ, φ (γ.toFun 0) ∂(eta l))
      ∧ (∫⁻ x, φ x ∂massMeasure = ∫⁻ γ, φ (γ.toFun γ.len) ∂(eta l))
  /-- Lemma A.5 (paper.tex line 1860): the marginal of `η_l` under restriction to the `j`-th unit
  subcurve, `j ∈ {1,…,l}`, coincides with `η_1`, stated for nonnegative measurable `h`. -/
  marginal : ∀ l j : ℕ, 1 ≤ j → j ≤ l → ∀ h : Curve E → ℝ≥0∞, Measurable h →
    ∫⁻ γ, h (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) ∂(eta l) = ∫⁻ γ, h γ ∂(eta 1)
