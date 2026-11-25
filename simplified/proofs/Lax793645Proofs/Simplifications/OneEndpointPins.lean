import Lax793645Proofs.Simplifications.OneFrameCoordinates
import Lax793645Proofs.Simplifications.QuadraticPinCaps
import Lax793645Proofs.Simplifications.ClosedImagePartitions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OneFull (p : Shape) (n : ℕ) := QuadraticFull (Ray p n) (Vec (Fin p.h))

def oneEndpointCoordinates (p : Shape) (n : ℕ) :
    Vec (OneColumn p n)≃ₗ[F](Bool→OneFull p n) where
  toFun v i:=(fun r=>v ⟨Sum.inl i,r⟩,
    (fun j=>v ⟨Sum.inr (Sum.inl i),j⟩,fun j=>v ⟨Sum.inr (Sum.inr i),j⟩))
  invFun v k:=match k with
    | ⟨Sum.inl i,r⟩=>v i |>.1 r
    | ⟨Sum.inr (Sum.inl i),j⟩=>((v i).2.1) j
    | ⟨Sum.inr (Sum.inr i),j⟩=>((v i).2.2) j
  left_inv v:=by
    funext k
    rcases k with ⟨i,k⟩
    rcases i with i|i
    · rfl
    · cases i <;> rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

variable {p : Shape} {n N : ℕ}

def oneEndpointProjection (i : Bool) : Vec (OneColumn p n)→ₗ[F]OneFull p n :=
  (LinearMap.proj i).comp (oneEndpointCoordinates p n).toLinearMap

def oneEndpointInjection (i : Bool) : OneFull p n→ₗ[F]Vec (OneColumn p n) :=
  (oneEndpointCoordinates p n).symm.toLinearMap.comp (LinearMap.single F (fun _ : Bool=>OneFull p n) i)

theorem one_endpoint_injection_projection (i j : Bool) (v : OneFull p n) :
    oneEndpointProjection j (oneEndpointInjection i v)=if i=j then v else 0 := by
  cases i <;> cases j <;> simp [oneEndpointProjection,oneEndpointInjection]

theorem one_endpoint_coordinate_sum (v : Vec (OneColumn p n)) :
    ∑ i,oneEndpointInjection i (oneEndpointProjection i v)=v := by
  apply (oneEndpointCoordinates p n).injective
  rw [map_sum]
  simp only [oneEndpointInjection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.single_apply]
  exact Finset.univ_sum_single _

theorem one_endpoint_images (x : OneUnit p n N) (e : Comp p.g) (i : Bool) (v : OneFull p n) :
    oneCoordinateImages x e*ᵥ(oneEndpointInjection i v)=oneAmbientCoordinates N (x i e v) := by
  rw [one_coordinate_images_apply]
  congr 1
  change (∑ j,x j e (oneEndpointProjection j (oneEndpointInjection i v)))=_
  simp only [one_endpoint_injection_projection]
  cases i <;> simp

/-- Closing the six coordinate blocks also closes either complete endpoint.
Thus projected primal and channel pins are actual stored pins. -/
theorem one_endpoint_pin_mem (P : Space (Vec (OneColumn p n)))
    (hP : coordinateClosure (oneBlockCoordinates p n) P=P)
    (i : Bool) {v : OneFull p n} (hv : v∈P.map (oneEndpointProjection i)) :
    oneEndpointInjection i v∈P := by
  obtain ⟨w,hw,rfl⟩:=hv
  rw [←hP]
  apply Submodule.mem_map.mpr
  refine ⟨oneBlockCoordinates p n (oneEndpointInjection i (oneEndpointProjection i w)),?_,
    (oneBlockCoordinates p n).symm_apply_apply _⟩
  apply Submodule.mem_pi.mpr
  intro b _
  have hh : oneBlockCoordinates p n w b∈
      (P.map (oneBlockCoordinates p n).toLinearMap).map (LinearMap.proj b):=
    ⟨oneBlockCoordinates p n w,⟨w,hw,rfl⟩,rfl⟩
  rcases b with j|j
  · by_cases h : i=j
    · subst j
      simpa [oneBlockCoordinates,oneEndpointInjection,oneEndpointProjection,oneEndpointCoordinates] using hh
    · convert (Submodule.zero_mem _) using 1
      ext r
      simp [oneBlockCoordinates,oneEndpointInjection,oneEndpointProjection,
        oneEndpointCoordinates,LinearMap.single_apply,h]
  · rcases j with j|j <;> by_cases h : i=j
    · subst j
      simpa [oneBlockCoordinates,oneEndpointInjection,oneEndpointProjection,oneEndpointCoordinates] using hh
    · convert (Submodule.zero_mem _) using 1
      ext r
      simp [oneBlockCoordinates,oneEndpointInjection,oneEndpointProjection,
        oneEndpointCoordinates,LinearMap.single_apply,h]
    · subst j
      simpa [oneBlockCoordinates,oneEndpointInjection,oneEndpointProjection,oneEndpointCoordinates] using hh
    · convert (Submodule.zero_mem _) using 1
      ext r
      simp [oneBlockCoordinates,oneEndpointInjection,oneEndpointProjection,
        oneEndpointCoordinates,LinearMap.single_apply,h]

theorem one_endpoint_pin_dimension (P : Space (Vec (OneColumn p n))) :
    dim P≤∑ i,dim (P.map (oneEndpointProjection i)) := by
  have h:=Submodule.finrank_mono (le_blockClosure (P.map (oneEndpointCoordinates p n).toLinearMap))
  change dim (P.map (oneEndpointCoordinates p n).toLinearMap)≤
    dim (blockClosure (P.map (oneEndpointCoordinates p n).toLinearMap)) at h
  rw [blockClosure_dimension] at h
  have he (i : Bool) : (P.map (oneEndpointCoordinates p n).toLinearMap).map (LinearMap.proj i)=
      P.map (oneEndpointProjection i) :=
    (Submodule.map_comp (oneEndpointCoordinates p n).toLinearMap (LinearMap.proj i) P).symm
  have h' : dim P≤∑ i,dim ((P.map (oneEndpointCoordinates p n).toLinearMap).map (LinearMap.proj i)):=by
    simpa only [dim,LinearEquiv.finrank_map_eq] using h
  exact h'.trans_eq (Finset.sum_congr rfl (fun i _=>congrArg (fun S : Space (OneFull p n)=>dim S) (he i)))

def oneEndpointTarget (T : Mat (Fin (2*N)) (OneColumn p n)) (i : Bool) : OneFrame p n N :=
  (oneAmbientCoordinates N).symm.toLinearMap.comp (T.mulVecLin.comp (oneEndpointInjection i))

theorem one_closed_pin_endpoint (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (ha : (onePinClosure p n).close a.sp=a.sp) (x : OneUnit p n N)
    (hx : imagePinAgree oneCoordinateImages a x) (i : Bool) (e : Comp p.g)
    {v : OneFull p n} (hv : v∈(a.sp e).map (oneEndpointProjection i)) :
    x i e v=oneEndpointTarget (a.target e) i v := by
  have h:=hx e (oneEndpointInjection i v)
    (one_endpoint_pin_mem (a.sp e) (congrFun ha e) i hv)
  rw [one_endpoint_images] at h
  exact (oneAmbientCoordinates N).injective (by
    simpa only [oneEndpointTarget,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply,Matrix.mulVecLin_apply] using h)

end
end Lax793645Proofs.Simplifications
