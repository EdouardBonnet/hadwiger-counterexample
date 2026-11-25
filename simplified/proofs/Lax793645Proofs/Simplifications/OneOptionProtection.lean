import Lax793645Proofs.Simplifications.OneOptionContracts
import Lax793645Proofs.Simplifications.IndependentOptionLabels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n K : ℕ}

structure OnePlanProtection (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) where
  bound : ∀ e,dim (a e)≤K
  selector : Space (Vec (SelIdx p.b p.j))
  base : Space (Vec (AIdx p.g n))
  selector_dim : dim selector≤oneSelectorProtectionDim p K
  base_dim : dim base≤oneBaseProtectionDim p K
  pin : ∀ i e,oneEndpointPrimalPins a i e≤tensorCross selector base
  low : ∀ i e x,x∈oneEndpointPrimalPins a i e→Matrix.rank (flattenMatrix.symm x)≤
    oneProtectionThreshold K 28→x∈tensorRectangle selector base

theorem one_plan_protection_exists (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (hK : ∀ e,dim (a e)≤K) : Nonempty (OnePlanProtection a K) := by
  obtain ⟨U,V,hU,hV,hpin,hlow⟩:=one_plan_protection a (oneProtectionThreshold K 28) K hK
  exact ⟨⟨hK,U,V,hU,hV,hpin,hlow⟩⟩

theorem OnePlanProtection.protect_template {a : ImagePlan (Comp p.g) (OneColumn p n)}
    (H : OnePlanProtection a K) {I : Type} [Fintype I] [DecidableEq I]
    (v : Template p I) (hI : Fintype.card I≤28)
    (hv : LinearIndependent F (H.selector.mkQ ∘ fun i=>selV p.j (v.s i))) :
    OnePenSpace v a K := by
  refine ⟨H.bound,H.selector,H.base,H.selector_dim,H.base_dim,H.pin,?_,hv⟩
  intro i e x hx hr
  apply H.low i e x hx (hr.trans ?_)
  unfold oneProtectionThreshold
  gcongr

include p n in
theorem one_messenger_card {q : Format} (h : ∀ i,1≤q i ∧ q i≤7) :
    Fintype.card (Messenger q)≤28 := by
  let v : Volley p n (Messenger q):=⟨parcel true,fun _=>0,fun _=>0⟩
  exact v.call_count (shots_ok true v rfl h)

end
end Lax793645Proofs.Simplifications
