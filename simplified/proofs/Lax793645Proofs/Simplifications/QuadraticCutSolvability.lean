import Lax793645Proofs.Simplifications.QuadraticChannelRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

theorem cut_matrix_functional_single (M : Profile p n) (e : Comp p.g) (W : Moment p n) :
    cutMatrixFunctional M (Pi.single e W)=mpair (M e) W := by
  classical
  rw [cut_matrix_functional_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [Pi.single_eq_of_ne hfe]
  · simp

def cutMatrixPairing : LinearMap.BilinForm F (Profile p n) where
  toFun:=cutMatrixFunctional
  map_add' A B:=LinearMap.ext (cut_matrix_functional_add A B)
  map_smul' c A:=by
    apply LinearMap.ext
    intro x
    simp [cut_matrix_functional_apply,mpair_smul,Finset.mul_sum]

theorem cut_matrix_pairing_nondegenerate : (cutMatrixPairing (p:=p) (n:=n)).Nondegenerate := by
  have kill (M : Profile p n) (h : ∀ x,cutMatrixFunctional M x=0) : M=0 := by
    funext e
    apply matrix_pairing_nondegenerate.1
    intro W
    exact (cut_matrix_functional_single M e W).symm.trans (h _)
  constructor
  · exact kill
  · intro M h
    apply kill M
    intro W
    have he : cutMatrixFunctional M W=cutMatrixFunctional W M := by
      simp only [cut_matrix_functional_apply]
      exact Finset.sum_congr rfl (fun e _=>mpair_comm _ _)
    exact he.trans (h W)

def quadraticCutConstraints (P K : Comp p.g→Space (Ray p n)) : Space (Profile p n) :=
  Submodule.pi Set.univ (fun e=>quadraticSquares (P e)⊔quadraticCross (K e))

theorem quadratic_cut_constraints_mem (P K : Comp p.g→Space (Ray p n)) (x : Profile p n) :
    x∈quadraticCutConstraints P K↔∀ e,x e∈quadraticSquares (P e)⊔quadraticCross (K e) := by
  simp [quadraticCutConstraints,Submodule.mem_pi]

theorem quadratic_cut_annihilator_values (P K : Comp p.g→Space (Ray p n)) (M : Profile p n) :
    (∀ x∈quadraticCutConstraints P K,cutMatrixFunctional M x=0)↔
      (∀ e,∀ v∈P e,(M e).toQuadraticForm' v=0) ∧
      (∀ e,∀ k∈K e,∀ v,(M e).toQuadraticForm'.polarBilin k v=0) := by
  classical
  constructor
  · intro h
    have he (e : Comp p.g) : ∀ W∈quadraticSquares (P e)⊔quadraticCross (K e),mpair (M e) W=0 := by
      intro W hW
      rw [←cut_matrix_functional_single]
      apply h
      rw [quadratic_cut_constraints_mem]
      intro f
      by_cases hf : f=e
      · subst f; simpa using hW
      · simp [Pi.single_eq_of_ne hf]
    exact ⟨fun e=>(quadratic_annihilator_values _ _ _).mp (he e) |>.1,
      fun e=>(quadratic_annihilator_values _ _ _).mp (he e) |>.2⟩
  · rintro ⟨hp,hk⟩ x hx
    rw [cut_matrix_functional_apply]
    apply Finset.sum_eq_zero
    intro e _
    exact (quadratic_annihilator_values _ _ _).mpr ⟨hp e,hk e⟩ _
      ((quadratic_cut_constraints_mem P K x).mp hx e)

/-- Solve all component quadratic equations jointly against the actual
cut-profile space. The only obstruction is the stated intersection. -/
theorem quadratic_cut_target_solvable (P K : Comp p.g→Space (Ray p n))
    (G : Xspace p n→ₗ[F]F)
    (hG : ∀ x : Xspace p n,x.val∈quadraticCutConstraints P K→G x=0) :
    ∃ M : Profile p n,(∀ x : Xspace p n,cutMatrixFunctional M x.val=G x) ∧
      (∀ e,∀ v∈P e,(M e).toQuadraticForm' v=0) ∧
      ∀ e,∀ k∈K e,∀ v,(M e).toQuadraticForm'.polarBilin k v=0 := by
  let T:=quadraticCutConstraints P K
  let f:=T.mkQ.comp (Xspace p n).subtype
  have hker : f.ker≤G.ker := by
    intro x hx
    exact hG x ((Submodule.Quotient.mk_eq_zero T).mp hx)
  obtain ⟨L,hL⟩:=mem_range_comp hker
  obtain ⟨M,hM⟩:=(cutMatrixPairing.toDual cut_matrix_pairing_nondegenerate).surjective
    (L.comp T.mkQ)
  change cutMatrixFunctional M=L.comp T.mkQ at hM
  refine ⟨M,?_,(quadratic_cut_annihilator_values P K M).mp ?_⟩
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
