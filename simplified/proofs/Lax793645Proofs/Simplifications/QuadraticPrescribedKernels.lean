import Lax793645Proofs.Simplifications.QuadraticCodeQuotients
import Lax793645Proofs.Simplifications.QuadraticPairGramLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R : Type} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] {N : ℕ}

theorem stack_matrix_kernel (z : Mat (Fin N) I×Mat (Fin N) I) :
    (stackMatrixEquiv N z).mulVecLin.ker=z.1.mulVecLin.ker⊓z.2.mulVecLin.ker := by
  ext v
  change (fromRows z.1 z.2)*ᵥv=0 ↔ z.1*ᵥv=0 ∧z.2*ᵥv=0
  rw [fromRows_mulVec]
  constructor
  · intro h
    exact ⟨congrArg (fun f : Vec (HyperbolicIdx N)=>f∘Sum.inl) h,
      congrArg (fun f : Vec (HyperbolicIdx N)=>f∘Sum.inr) h⟩
  · rintro ⟨h₁,h₂⟩
    rw [h₁,h₂]
    funext u
    cases u <;> rfl

theorem stack_matrix_quotient (L : Mat R I) (z : Mat (Fin N) R×Mat (Fin N) R) :
    stackMatrixEquiv N (z.1*L,z.2*L)=stackMatrixEquiv N z*L :=
  (Matrix.fromRows_mul _ _ _).symm

theorem quadratic_pair_quotient (L : Mat R I) (hL : Surjective L.mulVec)
    (z : Mat (Fin N) R×Mat (Fin N) R) (Q : Mat R R) :
    quadraticPairCode (z.1*L,z.2*L)=quadraticGramCode (Lᵀ*Q*L) ↔
      quadraticPairCode z=quadraticGramCode Q := by
  dsimp only [quadraticPairCode]
  have he : (z.1*L)ᵀ*(z.2*L)=Lᵀ*(z.1ᵀ*z.2)*L := by
    simp only [transpose_mul,Matrix.mul_assoc]
  rw [he]
  exact quadratic_quotient_code L hL _ Q

def quadraticPrescribedKernel (L : Mat R I) (Q : Mat R R)
    (z : Mat (Fin N) I×Mat (Fin N) I) : Prop:=
  (stackMatrixEquiv N z).mulVecLin.ker=L.mulVecLin.ker ∧
    quadraticPairCode z=quadraticGramCode (Lᵀ*Q*L)

/-- The quotient is used to count frames; the observation retains all
original columns, with one common physical-frame kernel. -/
def quadraticPrescribedEquiv (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R) :
    {z : Mat (Fin N) R×Mat (Fin N) R // quadraticPairGood Q z}≃
      {z : Mat (Fin N) I×Mat (Fin N) I // quadraticPrescribedKernel L Q z} := by
  classical
  let f (z : {z : Mat (Fin N) R×Mat (Fin N) R // quadraticPairGood Q z}) :
      {z : Mat (Fin N) I×Mat (Fin N) I // quadraticPrescribedKernel L Q z}:=
    ⟨(z.val.1*L,z.val.2*L),by
      rw [quadraticPrescribedKernel,stack_matrix_quotient,exact_kernel_mul_iff L hL,
        quadratic_pair_quotient L hL]
      exact z.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro z w h
    apply Subtype.ext
    apply Prod.ext
    · exact quotient_matrix_injective L hL (congrArg (fun z=>z.val.1) h)
    · exact quotient_matrix_injective L hL (congrArg (fun z=>z.val.2) h)
  · intro z
    have hk : L.mulVecLin.ker ≤ z.val.1.mulVecLin.ker⊓z.val.2.mulVecLin.ker := by
      rw [←stack_matrix_kernel,z.property.1]
    obtain ⟨X,hX⟩:=factor_through_quotient L z.val.1 (hk.trans inf_le_left)
    obtain ⟨Y,hY⟩:=factor_through_quotient L z.val.2 (hk.trans inf_le_right)
    have hz : quadraticPrescribedKernel L Q (X*L,Y*L):=by
      simpa only [hX,hY] using z.property
    have hi : Injective (stackMatrixEquiv N (X,Y)).mulVec := by
      have hh:=hz.1
      rw [stack_matrix_quotient L (X,Y),exact_kernel_mul_iff L hL] at hh
      exact hh
    have hg : quadraticPairCode (X,Y)=quadraticGramCode Q:=
      (quadratic_pair_quotient L hL (X,Y) Q).mp hz.2
    refine ⟨⟨(X,Y),hi,hg⟩,?_⟩
    apply Subtype.ext
    exact Prod.ext hX hY

theorem quadratic_prescribed_mass (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R) :
    pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (quadraticPrescribedKernel L Q)=
      bp (2*(N:ℝ)*(num R-num I))*
        pr (pairW unif unif : Wgt (Mat (Fin N) R×Mat (Fin N) R)) (quadraticPairGood Q) := by
  classical
  have hn : nbr (quadraticPrescribedKernel (N:=N) L Q)=nbr (quadraticPairGood (N:=N) Q) := by
    rw [nbr_eq_card,nbr_eq_card]
    exact_mod_cast Fintype.card_congr (quadraticPrescribedEquiv (N:=N) L hL Q).symm
  rw [←pair_unif,←pair_unif,pr_unif,pr_unif,hn]
  simp only [Fintype.card_prod,Nat.cast_mul]
  change _/(num (Mat (Fin N) I)*num (Mat (Fin N) I))=
    _*(_/(num (Mat (Fin N) R)*num (Mat (Fin N) R)))
  rw [cast_mat,cast_mat,←bp_add,←bp_add]
  have he : 2*(N:ℝ)*(num R-num I)=
      (num (Fin N)*num R+num (Fin N)*num R)-(num (Fin N)*num I+num (Fin N)*num I) := by
    simp only [num,Fintype.card_fin]
    ring
  rw [he,bp_sub]
  have hbp (x : ℝ) : bp x≠0:=(bp_pos x).ne'
  field_simp [hbp]

end
end Lax793645Proofs.Simplifications
