/- Adapts the finite tester calculation from the vendored Apache-2.0
OpenAI ZeroDiscrepancyPrediction module to the one-frame quadratic law. -/
import Lax793645Proofs.Simplifications.OneCommonPredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ZeroDiscrepancyPrediction

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneScreenRank (p : Shape) (K : ℕ) := (tagDegree p.g)*(2*p.h+2*p.J*K)
def oneScreen (p : Shape) (i : OneOrient p n N) (s : Label p.b) (E : Finset (Tag p.g)) (r : ℕ)
    (g : OneAugur p N) (δ : ℝ) :=
  ∃ w : Pdual p n,
    (∀ l f,pr (spins p n) (oneMismatch g w l s f i) ≤ δ)∧
    ∀ l : Tag p.g,
    ∃ M:Moment p n,M.rank ≤ r ∧ ∀ x : Knobs p.g n,
      let f:= Flavor.full
      let v:=spring p l s f x
      cleanInput p E x → w (useAtom p l s f x)=dialed p l f x+evmat M v v

theorem one_zero_screen (p : Shape) (x : OneUnit p n N) (i : Bool) (s : Label p.b)
    (m : Mixer p n) (α : F) (hg : Odd p.g)
    (U : Profile p n) (E : Finset (Tag p.g))
    (h : ∀ t,t∉E → role p n U+sharedT p n t U+α=1)
    (K : ℕ) (hk : totalRank U ≤ K) (g : OneAugur p N)
    (δ : ℝ) (L : Finset (Label p.b)) (hs : s∉ L)
    (hz : onePostulates (x i) g (oneYoke m x i U α) L δ) :
    oneScreen p (x i) s E (oneScreenRank p K) g δ := by
  classical
  let a := U; let f:=Flavor.full (g:=p.g)
  refine ⟨_,hz s hs,fun l=>?_⟩
  obtain ⟨M,hM,ht⟩:=one_inner_gem x i l
  refine ⟨M+qmix m a l,le_trans (mrk_add_le ..) ?_,fun y hy=>?_⟩
  · refine (Nat.add_le_add hM (qmix_rank ..)).trans ?_
    unfold oneScreenRank; change _+p.J*(tagDegree p.g)*(2*totalRank a)≤_
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (p.J*(tagDegree p.g))
      (Nat.mul_le_mul_left 2 hk)) _) (le_of_eq (by ring))
  let A:=useAtom p l s f y
  let z:=lit f l y; let T:=mom p s z
  have h0 : (Tsym m a+α • role p n) A= dialed p l f y+mpair (qmix m a l) T := by
    have hh : Tmix m a A=mpair (qmix m a l) T := Tmix_atom ..
    change T0 p n a A + Tmix m a A + α * role p n A=_
    rw [hh,add_right_comm]
    exact congrArg (·+_) (coreRole p U E α hg h l s y hy)
  change oneInner x i A + (Tsym m a + α • role p n) A = dialed p l f y+_
  rw [show oneInner x i A=mpair M T from ht s z,h0, ←mpair_outer,mpair_add]
  change mpair M T+(dialed p l f y + _) = dialed p l f y+(mpair M T+_)
  rw [add_left_comm]; rfl

end
end Lax793645Proofs.Simplifications
