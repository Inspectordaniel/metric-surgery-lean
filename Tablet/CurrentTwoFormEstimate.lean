import Tablet.CurrentFormAddF
import Tablet.CurrentFormAddPi
import Tablet.PiBoundsF
import Tablet.PiBoundsPi
import Tablet.psi
import Tablet.psiTilde
import Tablet.curveCurrent

-- [TABLET NODE: CurrentTwoFormEstimate]
/-- Paper.tex 1398-1407: the two-step multilinearity split of
`[[γ]](f,π) - [[γ]](f_k,π_j)` into `[[γ]](f-f_k,π) + [[γ]](f_k,π-π_j)`, followed by the two
Lemma A.2 estimates, packaged as a single per-curve bound by `ψ̃ + ψ`. Here `ω = (f,π)` is the
ambient `1`-form, `ωk = (f_k,π)` replaces only the `f`-slot, and `ωkj = (f_k,π_j)` replaces both;
the hypotheses say exactly that (`ωkj.f = ωk.f`, `ωk.pi = ω.pi`), that all six bound/Lipschitz
fields in play are `≤ C`, and that `f_k` (resp. `π_j`) is `ε`-close to `f` (resp. `π`) on the
finite set `Q`. -/
theorem CurrentTwoFormEstimate {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ωk ωkj : Form1 E)
    (hfk : ωkj.f = ωk.f) (hpik : ωk.pi = ω.pi)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfBk : (ωk.fBound : ℝ) ≤ C)
    (hfL : (ω.fLip : ℝ) ≤ C) (hfLk : (ωk.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C) (hpLk : (ωk.piLip : ℝ) ≤ C) (hpLkj : (ωkj.piLip : ℝ) ≤ C)
    (hQf : ∀ q ∈ Q, |ω.f q - ωk.f q| ≤ ε)
    (hQpi : ∀ q ∈ Q, |ω.pi q - ωkj.pi q| ≤ ε) :
    |curveCurrent γ ω - curveCurrent γ ωkj| ≤ psiTilde m Q ε C γ + psi m Q ε C γ := by
-- BODY
  set D1 : Form1 E :=
    { f := fun x => ω.f x - ωk.f x,
      fBound := ω.fBound + ωk.fBound,
      f_bounded := fun x => (abs_sub _ _).trans
        (by push_cast; exact add_le_add (ω.f_bounded x) (ωk.f_bounded x)),
      fLip := ω.fLip + ωk.fLip,
      f_lipschitz := ω.f_lipschitz.sub ωk.f_lipschitz,
      pi := ω.pi, piLip := ω.piLip, pi_lipschitz := ω.pi_lipschitz } with hD1
  set D2 : Form1 E :=
    { f := ωk.f, fBound := ωk.fBound, f_bounded := ωk.f_bounded,
      fLip := ωk.fLip, f_lipschitz := ωk.f_lipschitz,
      pi := fun x => ωk.pi x - ωkj.pi x,
      piLip := ωk.piLip + ωkj.piLip,
      pi_lipschitz := ωk.pi_lipschitz.sub ωkj.pi_lipschitz } with hD2
  have hAF : curveCurrent γ ω = curveCurrent γ D1 + curveCurrent γ ωk :=
    CurrentFormAddF γ D1 ωk ω rfl hpik
      (fun x => by show ω.f x = (ω.f x - ωk.f x) + ωk.f x; ring)
  have hAPi : curveCurrent γ ωk = curveCurrent γ D2 + curveCurrent γ ωkj :=
    CurrentFormAddPi γ D2 ωkj ωk rfl hfk
      (fun x => by show ωk.pi x = (ωk.pi x - ωkj.pi x) + ωkj.pi x; ring)
  have hBF : |curveCurrent γ D1| ≤ psiTilde m Q ε C γ :=
    PiBoundsF γ m hm Q hQne ε C hε hC ω ωk hfB hfBk hfL hfLk hpL hQf
  have hQpi' : ∀ q ∈ Q, |ωk.pi q - ωkj.pi q| ≤ ε := by
    intro q hq; rw [hpik]; exact hQpi q hq
  have hBPi : |curveCurrent γ D2| ≤ psi m Q ε C γ :=
    PiBoundsPi γ m hm Q hQne ε C hε hC ωk ωkj hfBk hfLk hpLk hpLkj hQpi'
  have hsplit : curveCurrent γ ω - curveCurrent γ ωkj = curveCurrent γ D1 + curveCurrent γ D2 := by
    rw [hAF, hAPi]; ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hBF hBPi)
