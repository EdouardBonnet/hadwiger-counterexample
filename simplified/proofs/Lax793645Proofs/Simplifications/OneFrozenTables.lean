import Lax793645Proofs.Simplifications.OneReciprocalRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def onePrimalPins (P : ImagePlan (Comp p.g) (OneColumn p n)) (e : Comp p.g) : Space (JointRay p n):=
  (P e).map ((LinearMap.fst F _ _).comp (oneNominalCoordinates p n).toLinearMap)

def oneChannelPins (P : ImagePlan (Comp p.g) (OneColumn p n)) (i : Bool) (e : Comp p.g) :
    Space (Hyperbolic p.h):=
  (P e).map ((LinearMap.proj i).comp ((LinearMap.snd F _ _).comp (oneNominalCoordinates p n).toLinearMap))

theorem one_primal_pin_dimension (P : ImagePlan (Comp p.g) (OneColumn p n)) (e : Comp p.g) :
    dim (onePrimalPins P e)≤dim (P e):=Submodule.finrank_map_le _ _

theorem one_channel_pin_dimension (P : ImagePlan (Comp p.g) (OneColumn p n))
    (i : Bool) (e : Comp p.g) : dim (oneChannelPins P i e)≤dim (P e):=Submodule.finrank_map_le _ _

theorem one_table_nominal_value (Q : OneCross p n) (e : Comp p.g)
    (v w : Vec (OneColumn p n)) :
    oneTableOfCross Q e (oneNominalCoordinates p n v) (oneNominalCoordinates p n w)=
      evmat (Q e) v w := by
  simp only [oneTableOfCross,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,Matrix.toBilin'_apply']
  rfl

theorem one_frozen_table_rows (P : ImagePlan (Comp p.g) (OneColumn p n)) (Q S : OneCross p n)
    (h : ∀ e a c,a∈onePrimalPins P e→(∀ i,c i∈oneChannelPins P i e)→∀ v,
      oneTableOfCross Q e (a,c) v=oneTableOfCross S e (a,c) v) :
    imageRowAgree P Q S := by
  intro e v hv w
  have ha : (oneNominalCoordinates p n v).1∈onePrimalPins P e:=⟨v,hv,rfl⟩
  have hc (i : Bool) : (oneNominalCoordinates p n v).2 i∈oneChannelPins P i e:=⟨v,hv,rfl⟩
  have he:=h e _ _ ha hc (oneNominalCoordinates p n w)
  simpa only [Prod.mk.eta,one_table_nominal_value] using he

theorem one_frozen_table_columns (P : ImagePlan (Comp p.g) (OneColumn p n)) (Q S : OneCross p n)
    (h : ∀ e b d,b∈onePrimalPins P e→(∀ j,d j∈oneChannelPins P j e)→∀ v,
      oneTableOfCross Q e v (b,d)=oneTableOfCross S e v (b,d)) :
    imageRowAgree P (fun e=>(Q e)ᵀ) (fun e=>(S e)ᵀ) := by
  intro e v hv w
  rw [evmat_transpose,evmat_transpose]
  have hb : (oneNominalCoordinates p n v).1∈onePrimalPins P e:=⟨v,hv,rfl⟩
  have hd (i : Bool) : (oneNominalCoordinates p n v).2 i∈oneChannelPins P i e:=⟨v,hv,rfl⟩
  have he:=h e _ _ hb hd (oneNominalCoordinates p n w)
  simpa only [Prod.mk.eta,one_table_nominal_value] using he

variable {I : Type} [Fintype I]

/-- Turn the relative quadratic realization into the exact promise
consumed by single-frame collision counting, including both frozen sides. -/
theorem one_build_realized_table (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (x y : OneUnit p n N)
    (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (MA MB : Bool→JointProfile p n) (f c r : ℕ)
    (hPA : ∀ e,dim (onePrimalPins a e)≤f) (hPB : ∀ e,dim (onePrimalPins b e)≤f)
    (hCA : ∀ i e,dim (oneChannelPins a i e)≤c) (hCB : ∀ j e,dim (oneChannelPins b j e)≤c)
    (hMA : ∀ j e,(MA j e).rank≤r) (hMB : ∀ i e,(MB i e).rank≤r)
    (hgradA : ∀ i j,∀ z∈Xspace p n,jointMatrixFunctional (MA j) (jointEndpointMap i z)=
      grad m (v.sumAt t w.obj i j) z)
    (hgradB : ∀ j i,∀ z∈Xspace p n,jointMatrixFunctional (MB i) (jointEndpointMap j z)=
      grad m (w.sumAt t v.obj j i) z)
    (hobsA : ∀ j z,z∈jointXspace→
      z∈jointQuadraticConstraints (onePrimalPins a) (fun e=>frozenChannelKernel p.h
        (onePrimalPins a e) (oneChannelPins b j e)
        ((unitLeftChannels p.h (oneUnitActual x y e) j).domRestrict (onePrimalPins a e)))→
      jointMatrixFunctional (MA j) z=jointMatrixFunctional
        (fun e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j)) z)
    (hobsB : ∀ i z,z∈jointXspace→
      z∈jointQuadraticConstraints (onePrimalPins b) (fun e=>frozenChannelKernel p.h
        (onePrimalPins b e) (oneChannelPins a i e)
        ((unitRightChannels p.h (oneUnitActual x y e) i).domRestrict (onePrimalPins b e)))→
      jointMatrixFunctional (MB i) z=jointMatrixFunctional
        (fun e=>channelQuadraticMatrix p.h (unitRightChannels p.h (oneUnitActual x y e) i)) z)
    (hroom : r+(f+c)+jointCompressionRank p f (2*f+(f+c))+5*c+6*f+2≤p.h) :
    ∃ Q : OneCross p n,OneRealized v w t m Q ∧
      imageRowAgree a Q (oneCrossMatrix x y) ∧
      imageRowAgree b (fun e=>(Q e)ᵀ) (oneCrossMatrix y x) := by
  obtain ⟨Q,QA,QB,hqA,hqB,hoA,hoB,hrow,hcol⟩:=one_reciprocal_realization
    (oneUnitActual x y) (onePrimalPins a) (onePrimalPins b) (oneChannelPins a) (oneChannelPins b)
    MA MB f c r hPA hPB hCA hCB hMA hMB hobsA hobsB hroom
  refine ⟨Q,⟨QA,QB,hqA,hqB,?_,?_⟩,?_,?_⟩
  · intro i j z hz
    exact (hoA j _ (joint_endpoint_in_space i z hz)).trans (hgradA i j z hz)
  · intro j i z hz
    exact (hoB i _ (joint_endpoint_in_space j z hz)).trans (hgradB j i z hz)
  · apply one_frozen_table_rows a Q (oneCrossMatrix x y)
    simpa only [one_actual_table] using hrow
  · have he:=one_frozen_table_columns b Q (oneCrossMatrix x y)
      (by simpa only [one_actual_table] using hcol)
    simpa only [one_cross_reciprocal] using he

end
end Lax793645Proofs.Simplifications
