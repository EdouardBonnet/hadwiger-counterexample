import Lax793645Proofs.Simplifications.OneSelectedObstructions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- Actual reciprocal realization from the scalar value tests. The
annihilator, bounded-rank compression and relative quadratic extensions
are discharged inside the theorem; no realization oracle is assumed. -/
theorem one_build_selected_table
    (v w : Volley p n I) (t : Tagging p I) (hv : v.legal t) (hw : w.legal t) (m : Mixer p n)
    (x y : OneUnit p n N) (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (PA PB : Bool→Comp p.g→Space (Ray p n)) (R : ℕ)
    (hprotA : OneProtectedVolley v t PA R) (hprotB : OneProtectedVolley w t PB R)
    (hpinA : onePrimalPins a=oneSelectedPrimal v t PA)
    (hpinB : onePrimalPins b=oneSelectedPrimal w t PB)
    (hsafeA : onePinSafe PA (oneChannelPins b) x y)
    (hsafeB : onePinSafe PB (oneChannelPins a) y x)
    (MA MB : Bool→JointProfile p n) (f c r : ℕ)
    (hFA : ∀ e,dim (onePrimalPins a e)≤f) (hFB : ∀ e,dim (onePrimalPins b e)≤f)
    (hCA : ∀ i e,dim (oneChannelPins a i e)≤c) (hCB : ∀ j e,dim (oneChannelPins b j e)≤c)
    (hMA : ∀ j e,(MA j e).rank≤r) (hMB : ∀ i e,(MB i e).rank≤r)
    (hgradA : ∀ i j,∀ z∈Xspace p n,jointMatrixFunctional (MA j) (jointEndpointMap i z)=
      grad m (v.sumAt t w.obj i j) z)
    (hgradB : ∀ j i,∀ z∈Xspace p n,jointMatrixFunctional (MB i) (jointEndpointMap j z)=
      grad m (w.sumAt t v.obj j i) z)
    (hatomA : ∀ j q,jointMatrixFunctional (MA j) (jointEndpointMap (v.obj q) (v.atomAt t q))=
      jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h
        (unitLeftChannels p.h (oneUnitActual x y e) j))
        (jointEndpointMap (v.obj q) (v.atomAt t q)))
    (hatomB : ∀ i q,jointMatrixFunctional (MB i) (jointEndpointMap (w.obj q) (w.atomAt t q))=
      jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h
        (unitRightChannels p.h (oneUnitActual x y e) i))
        (jointEndpointMap (w.obj q) (w.atomAt t q)))
    (heffectiveA : ∀ j z,z∈jointXspace→
      (∀ e,z e∈quadraticSquares (jointSpace (fun i=>PA i e)))→
      jointMatrixFunctional (MA j) z=jointMatrixFunctional
        (fun e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j)) z)
    (heffectiveB : ∀ i z,z∈jointXspace→
      (∀ e,z e∈quadraticSquares (jointSpace (fun j=>PB j e)))→
      jointMatrixFunctional (MB i) z=jointMatrixFunctional
        (fun e=>channelQuadraticMatrix p.h (unitRightChannels p.h (oneUnitActual x y e) i)) z)
    (hroom : r+(f+c)+jointCompressionRank p f (2*f+(f+c))+5*c+6*f+2≤p.h) :
    ∃ Q : OneCross p n,OneRealized v w t m Q ∧
      imageRowAgree a Q (oneCrossMatrix x y) ∧
      imageRowAgree b (fun e=>(Q e)ᵀ) (oneCrossMatrix y x) := by
  apply one_build_realized_table v w t m x y a b MA MB f c r hFA hFB hCA hCB hMA hMB
    hgradA hgradB ?_ ?_ hroom
  · rw [hpinA]
    exact one_selected_obstructions v t hv PA R hprotA (oneChannelPins b)
      (fun j e=>unitLeftChannels p.h (oneUnitActual x y e) j) hsafeA MA hatomA heffectiveA
  · rw [hpinB]
    simp_rw [one_right_channels_reciprocal] at hatomB heffectiveB ⊢
    exact one_selected_obstructions w t hw PB R hprotB (oneChannelPins a)
      (fun i e=>unitLeftChannels p.h (oneUnitActual y x e) i) hsafeB MB hatomB heffectiveB

end
end Lax793645Proofs.Simplifications
