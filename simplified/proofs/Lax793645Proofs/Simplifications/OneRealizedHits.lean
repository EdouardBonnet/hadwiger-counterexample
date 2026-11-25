import Lax793645Proofs.Simplifications.OneChannelTests
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CellPruning

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

/-- The quadratic replacement for the two derivative-realization
promises. All four reciprocal endpoint demands are checked on Xspace. -/
structure OneRealized (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (Q : OneCross p n) : Prop where
  certificate : ∃ QA QB : Bool→JointProfile p n,
    (∀ j e a,hyperbolicQuadratic p.h (unitLeftChannels p.h (oneTableOfCross Q e) j a)=
      (QA j e).toQuadraticForm' a) ∧
    (∀ i e b,hyperbolicQuadratic p.h (unitRightChannels p.h (oneTableOfCross Q e) i b)=
      (QB i e).toQuadraticForm' b) ∧
    (∀ i j,∀ z∈Xspace p n,jointMatrixFunctional (QA j) (jointEndpointMap i z)=
      grad m (v.sumAt t w.obj i j) z) ∧
    (∀ j i,∀ z∈Xspace p n,jointMatrixFunctional (QB i) (jointEndpointMap j z)=
      grad m (w.sumAt t v.obj j i) z)

theorem one_channel_match_conflicts (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (x y : OneUnit p n N) (hv : v.legal t) (hw : w.legal t)
    (hx : ∀ i,oneFrameLaw m (x i)) (hy : ∀ j,oneFrameLaw m (y j))
    (hk : oneVolleyKeys v t x=oneVolleyKeys w t y) (hrole : v.roleMatch w t)
    (Q : OneCross p n) (hQ : OneRealized v w t m Q)
    (ht : oneChannelTest (oneCrossMatrix x y)=oneChannelTest Q) :
    (oneRawHoles m).conflict (x true,x false) (y true,y false) := by
  obtain ⟨QA,QB,hQA,hQB,hA,hB⟩:=hQ.certificate
  exact one_unit_realized_conflicts v w t m x y hv hw hx hy hk hrole
    (fun e=>unitPrimalTable p.h (oneUnitActual x y e))
    (fun e=>unitChannelTable p.h (oneUnitActual x y e))
    (fun j e=>unitLeftChannels p.h (oneTableOfCross Q e) j)
    (fun i e=>unitRightChannels p.h (oneTableOfCross Q e) i)
    QA QB (one_test_actual_channels x y Q ht) hQA hQB hA hB

/-- A realized table gives a quantitative conflict probability under the
actual one-frame geometry. The two leaves remain independently sampled. -/
theorem one_realized_conflict_hit (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (hv : v.legal t) (hw : w.legal t) (hrole : v.roleMatch w t)
    (Q : OneCross p n) (hQ : OneRealized v w t m Q)
    {α β : Wgt (OneUnit p n N)} (hα : IsLaw α) (hβ : IsLaw β)
    {a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)}
    (hc : imagePinClear oneCoordinateImages a 0.05 α)
    (hd : imagePinClear oneCoordinateImages b 0.05 β)
    (hA : ∀ x,α x≠0→∀ i,oneFrameLaw m (x i))
    (hB : ∀ y,β y≠0→∀ i,oneFrameLaw m (y i))
    (hkey : ∀ x,α x≠0→∀ y,β y≠0→ oneVolleyKeys v t x=oneVolleyKeys w t y)
    (hrow : ∀ x,α x≠0→∀ y,β y≠0→imageRowAgree a.sp (oneCrossMatrix x y) Q ∧
      imageRowAgree b.sp (fun e=>(oneCrossMatrix x y e)ᵀ) (fun e=>(Q e)ᵀ))
    (hN : 100≤2*N) (hT : (dim (OneCheckGram p n):ℝ)≤0.01*(2*N)) :
    hit (2*N)≤pr (pairW α β)
      (fun xy=>(oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false)) := by
  apply (one_gram_hit Q oneChannelTest hα hβ hc hd hrow hN hT).trans
  apply pr_on_mono (pairW_law hα hβ).nz
  rintro ⟨x,y⟩ hxy ht
  have hx:=left_ne_zero_of_mul hxy
  have hy:=right_ne_zero_of_mul hxy
  exact one_channel_match_conflicts v w t m x y hv hw (hA x hx) (hB y hy)
    (hkey x hx y hy) hrole Q hQ ht

end
end Lax793645Proofs.Simplifications
