import Lax793645Proofs.Simplifications.JointQuadraticCuts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

def jointCutMap : (Bool→Profile p n)→ₗ[F]JointProfile p n where
  toFun:=jointCutEmbed
  map_add' x y:=by
    funext e
    exact Matrix.blockDiagonal_add _ _
  map_smul' c x:=by
    funext e
    exact Matrix.blockDiagonal_smul c _

def jointXspace : Space (JointProfile p n) :=
  (Submodule.pi Set.univ (fun _ : Bool=>Xspace p n)).map jointCutMap

theorem joint_xspace_mem (x : JointProfile p n) :
    x∈jointXspace↔∃ y : Bool→Profile p n,(∀ i,y i∈Xspace p n) ∧ jointCutEmbed y=x := by
  simp only [jointXspace,Submodule.mem_map,Submodule.mem_pi,Set.mem_univ,true_implies]
  rfl

theorem joint_cut_in_space (x : Bool→Profile p n) (hx : ∀ i,x i∈Xspace p n) :
    jointCutEmbed x∈jointXspace := (joint_xspace_mem _).mpr ⟨x,hx,rfl⟩

def jointEndpointMap (i : Bool) : Profile p n→ₗ[F]JointProfile p n :=
  jointCutMap.comp (LinearMap.single F (fun _ : Bool=>Profile p n) i)

theorem joint_cut_endpoint_sum (x : Bool→Profile p n) :
    jointCutEmbed x=∑ i,jointEndpointMap i (x i) := by
  change jointCutMap x=∑ i : Bool,jointCutMap (Pi.single i (x i))
  rw [←map_sum,LinearMap.sum_single_apply]

theorem joint_endpoint_in_space (i : Bool) (x : Profile p n) (hx : x∈Xspace p n) :
    jointEndpointMap i x∈jointXspace := by
  apply joint_cut_in_space
  intro j
  by_cases hj : j=i
  · subst j; simpa using hx
  · simp [LinearMap.single_apply,Pi.single_eq_of_ne hj]

def jointMatrixFunctional (M : JointProfile p n) : JointProfile p n→ₗ[F]F :=
  ∑ e,(mpair (M e)).comp (LinearMap.proj e)

theorem joint_matrix_functional_apply (M x : JointProfile p n) :
    jointMatrixFunctional M x=∑ e,mpair (M e) (x e) := by
  simp only [jointMatrixFunctional,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]

theorem joint_matrix_functional_add (A B x : JointProfile p n) :
    jointMatrixFunctional (A+B) x=jointMatrixFunctional A x+jointMatrixFunctional B x := by
  simp only [joint_matrix_functional_apply,Pi.add_apply,mpair_add,Finset.sum_add_distrib]

theorem joint_matrix_functional_single (M : JointProfile p n) (e : Comp p.g)
    (W : JointMoment p n) : jointMatrixFunctional M (Pi.single e W)=mpair (M e) W := by
  classical
  rw [joint_matrix_functional_apply,Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [Pi.single_eq_of_ne hfe]
  · simp

def jointMatrixPairing : LinearMap.BilinForm F (JointProfile p n) where
  toFun:=jointMatrixFunctional
  map_add' A B:=LinearMap.ext (joint_matrix_functional_add A B)
  map_smul' c A:=by
    apply LinearMap.ext
    intro x
    simp [joint_matrix_functional_apply,mpair_smul,Finset.mul_sum]

theorem joint_matrix_pairing_nondegenerate :
    (jointMatrixPairing (p:=p) (n:=n)).Nondegenerate := by
  have kill (M : JointProfile p n) (h : ∀ x,jointMatrixFunctional M x=0) : M=0 := by
    funext e
    apply matrix_pairing_nondegenerate.1
    intro W
    exact (joint_matrix_functional_single M e W).symm.trans (h _)
  constructor
  · exact kill
  · intro M h
    apply kill M
    intro W
    have he : jointMatrixFunctional M W=jointMatrixFunctional W M := by
      simp only [joint_matrix_functional_apply]
      exact Finset.sum_congr rfl (fun e _=>mpair_comm _ _)
    exact he.trans (h W)

def jointQuadraticConstraints (P K : Comp p.g→Space (JointRay p n)) :
    Space (JointProfile p n) :=
  Submodule.pi Set.univ (fun e=>quadraticSquares (P e)⊔quadraticCross (K e))

theorem joint_quadratic_constraints_mem (P K : Comp p.g→Space (JointRay p n))
    (x : JointProfile p n) : x∈jointQuadraticConstraints P K↔
      ∀ e,x e∈quadraticSquares (P e)⊔quadraticCross (K e) := by
  simp [jointQuadraticConstraints,Submodule.mem_pi]

theorem joint_quadratic_annihilator_values (P K : Comp p.g→Space (JointRay p n))
    (M : JointProfile p n) :
    (∀ x∈jointQuadraticConstraints P K,jointMatrixFunctional M x=0)↔
      (∀ e,∀ v∈P e,(M e).toQuadraticForm' v=0) ∧
      (∀ e,∀ k∈K e,∀ v,(M e).toQuadraticForm'.polarBilin k v=0) := by
  classical
  constructor
  · intro h
    have he (e : Comp p.g) : ∀ W∈quadraticSquares (P e)⊔quadraticCross (K e),
        mpair (M e) W=0 := by
      intro W hW
      rw [←joint_matrix_functional_single]
      apply h
      rw [joint_quadratic_constraints_mem]
      intro f
      by_cases hf : f=e
      · subst f; simpa using hW
      · simp [Pi.single_eq_of_ne hf]
    exact ⟨fun e=>(quadratic_annihilator_values _ _ _).mp (he e) |>.1,
      fun e=>(quadratic_annihilator_values _ _ _).mp (he e) |>.2⟩
  · rintro ⟨hp,hk⟩ x hx
    rw [joint_matrix_functional_apply]
    apply Finset.sum_eq_zero
    intro e _
    exact (quadratic_annihilator_values _ _ _).mpr ⟨hp e,hk e⟩ _
      ((joint_quadratic_constraints_mem P K x).mp hx e)

theorem joint_quadratic_target_solvable (P K : Comp p.g→Space (JointRay p n))
    (G : jointXspace (p:=p) (n:=n)→ₗ[F]F)
    (hG : ∀ x : jointXspace,x.val∈jointQuadraticConstraints P K→G x=0) :
    ∃ M : JointProfile p n,(∀ x : jointXspace,jointMatrixFunctional M x.val=G x) ∧
      (∀ e,∀ v∈P e,(M e).toQuadraticForm' v=0) ∧
      ∀ e,∀ k∈K e,∀ v,(M e).toQuadraticForm'.polarBilin k v=0 := by
  let T:=jointQuadraticConstraints P K
  let f:=T.mkQ.comp jointXspace.subtype
  have hker : f.ker≤G.ker := by
    intro x hx
    exact hG x ((Submodule.Quotient.mk_eq_zero T).mp hx)
  obtain ⟨L,hL⟩:=mem_range_comp hker
  obtain ⟨M,hM⟩:=(jointMatrixPairing.toDual joint_matrix_pairing_nondegenerate).surjective
    (L.comp T.mkQ)
  change jointMatrixFunctional M=L.comp T.mkQ at hM
  refine ⟨M,?_,(joint_quadratic_annihilator_values P K M).mp ?_⟩
  · intro x
    rw [hM]
    exact LinearMap.congr_fun hL x
  · intro x hx
    rw [hM]
    change L (T.mkQ x)=0
    have hz : T.mkQ x=0:=(Submodule.Quotient.mk_eq_zero T).mpr hx
    rw [hz,map_zero]

end
end Lax793645Proofs.Simplifications
