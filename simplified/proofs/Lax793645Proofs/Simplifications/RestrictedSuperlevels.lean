import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SuperlevelBounds

/-! Superlevel sets restricted to a fixed predictor cell. The net is still a
net for every filter on the independently drawn B leaf; no conditioning on a
compatible pair is used to choose it. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
variable {A : Type} [Fintype A]

theorem cliff_thick_on (P : Wgt A → Prop) (x f u : Wgt A) (E : A → Prop)
    (hu : IsLaw u) (hx : ∀ a, 0 ≤ x a) (hp : P x) (t δ : ℝ)
    (ht : 0 < t) (hs : smallSet P u δ t) (hw : varOne x f ≤ t)
    (h : 5*t ≤ pr x E) :
    δ < pr u (fun a => E a ∧ cliff u f t a) := by
  classical
  by_contra! hh
  have he := hs x hp (fun a => E a ∧ cliff u f t a) hh
  have hg := (cliff_bounds u f x t t ht hu hw).1
  have hi := pr_shield hx E (cliff u f t)
  linarith

theorem cliff_score_on (P : Wgt A → Prop) (x y f u : Wgt A) (E : A → Prop)
    (hx : SubLaw x) (hy : SubLaw y) (hu : IsLaw u) (hz : lsupp x u)
    (K t ε : ℝ) (ht : 0 < t) (h1 : P x) (hf : varOne y f ≤ ε)
    (h2 : smallSet P u (ε/t) K)
    (h : 2*K ≤ pr x (fun a => E a ∧ cliff u f t a)) :
    t*K ≤ overlap u x y :=
  cliff_score P x y f u hx hy hu hz K t ε ht h1 hf h2
    (h.trans (pr_mono hx.nz fun _ h => h.2))

end
end Lax793645Proofs.Simplifications
