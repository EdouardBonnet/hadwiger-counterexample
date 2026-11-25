import Lax793645Proofs.Simplifications.OneProtectedKeys
import Lax793645Proofs.Simplifications.ProtectedBaseSampling

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def oneProtectionThreshold (K t : ℕ):=(4*(K+t))^2+t
def oneSelectorProtectionDim (p : Shape) (K : ℕ):=
  oneProtectionThreshold K 28*(Fintype.card (Bool×Comp p.g)*K)
def oneBaseProtectionDim (p : Shape) (K : ℕ):=
  Fintype.card (SelIdx p.b p.j)*(Fintype.card (Bool×Comp p.g)*K)

def OnePenSpace (v : Template p I) (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) : Prop :=
  (∀ e,dim (a e)≤K) ∧
  ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
    dim U≤oneSelectorProtectionDim p K ∧ dim V≤oneBaseProtectionDim p K ∧
    (∀ i e,oneEndpointPrimalPins a i e≤tensorCross U V) ∧
    (∀ i e x,x∈oneEndpointPrimalPins a i e→
      Matrix.rank (flattenMatrix.symm x)≤oneProtectionThreshold K (Fintype.card I)→
      x∈tensorRectangle U V) ∧
    LinearIndependent F (U.mkQ ∘ (fun j=>selV p.j (v.s j)))

def OneProtectedInput (v : Template p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) (x : Inputs p n I) : Prop :=
  Nonempty (OneProtectedVolley (v.draw x) v.t (oneEndpointPrimalPins a)
    (4*(K+Fintype.card I)))

/-- The only random protection test is independence of base vectors.
It is charged against the raw input law before orientation acceptance. -/
theorem one_query_rejection (v : Template p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (hpen : OnePenSpace v a K) (z : I→F)
    (hz : ∀ i,IsLaw (scopedBit p n (v.t i) (v.f i) (z i))) :
    pr (v.state z n) (fun x=>¬OneProtectedInput v a K x)≤
      bp (num I+(oneBaseProtectionDim p K:ℝ)-(n:ℝ)) := by
  obtain ⟨hK,U,V,_,hV,hcross,hlow,hs⟩:=hpen
  have hsub : pr (v.state z n) (fun x=>¬OneProtectedInput v a K x)≤
      pr (v.state z n) (fun x=>¬LinearIndependent F
        (V.mkQ ∘ (fun j=>baseV ((v.draw x).par j)))) := by
    apply pr_mono (prodW_law hz).nz
    intro x hx hb
    apply hx
    refine ⟨one_protected_volley (v.draw x) v.t a K hK U V hcross hlow ?_ ?_⟩
    · intro i
      exact hs.comp (fun j : CallsAt (v.draw x) i=>j.val) Subtype.val_injective
    · intro i
      exact hb.comp (fun j : CallsAt (v.draw x) i=>j.val) Subtype.val_injective
  apply hsub.trans ((template_base_rejection v z hz V).trans (bp_le ?_))
  have hh : (dim V:ℝ)≤oneBaseProtectionDim p K:=by exact_mod_cast hV
  linarith

end
end Lax793645Proofs.Simplifications
