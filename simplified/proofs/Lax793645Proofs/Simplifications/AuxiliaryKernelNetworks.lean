import Lax793645Proofs.Simplifications.AuxiliaryKernelCertificate
import Lax793645Proofs.Simplifications.QuadraticNetworkNormalization
import Lax793645Proofs.Simplifications.NetworkSieveLaw

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R G : Type} [Fintype I] [Fintype R] [Fintype G]
  [DecidableEq I] [DecidableEq R] [DecidableEq G] {N : ℕ}

def auxiliaryPairing (x y : Rack I N) : Mat I I:=x.1ᵀ*y.2+x.2ᵀ*y.1

theorem stacked_auxiliary_pairing (x y : Rack I N) :
    (Matrix.fromRows x.1 x.2)ᵀ*(Matrix.fromRows y.2 y.1)=auxiliaryPairing x y := by
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.transpose_apply,
    auxiliaryPairing,Matrix.add_apply]
  rfl

/-- The certificate in the actual one-frame coordinates. Swapping the
two halves of each auxiliary vector changes the dot product into the
ambient polar pairing. -/
theorem auxiliary_pair_kernel (L : Mat R I) (hL : Surjective L.mulVec) (x : Rack I N) :
    ind ((Matrix.fromRows x.1 x.2).mulVecLin.ker=L.mulVecLin.ker)=
      bp (num I*num R)*ind (L.mulVecLin.ker≤x.1.mulVecLin.ker ∧
        L.mulVecLin.ker≤x.2.mulVecLin.ker)*
      pr unif (fun y : Rack I N=>auxiliaryPairing x y=Lᵀ*L) := by
  have hh:=auxiliary_kernel_certificate L hL (Matrix.fromRows x.1 x.2)
  have hk : L.mulVecLin.ker≤(Matrix.fromRows x.1 x.2).mulVecLin.ker ↔
      L.mulVecLin.ker≤x.1.mulVecLin.ker ∧ L.mulVecLin.ker≤x.2.mulVecLin.ker:=by
    change L.mulVecLin.ker≤(stackMatrixEquiv N x).mulVecLin.ker ↔ _
    rw [stack_matrix_kernel,le_inf_iff]
  rw [hk] at hh
  have he:=probability_equiv ((Equiv.prodComm _ _).trans (stackMatrixEquiv (I:=I) N))
    (fun Y : Mat (HyperbolicIdx N) I=>(Matrix.fromRows x.1 x.2)ᵀ*Y=Lᵀ*L)
  have hv (y : Rack I N) :
      (Matrix.fromRows x.1 x.2)ᵀ*((Equiv.prodComm _ _).trans (stackMatrixEquiv (I:=I) N) y)=
        auxiliaryPairing x y:=stacked_auxiliary_pairing x y
  simp_rw [hv] at he
  rw [←he] at hh
  exact hh

variable (g : Route I G) {H : G→Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

def auxiliaryNetworkPairing (L : ∀ i,Mat (H i) (Port g i))
    (x y : Rack I N) : Prop:=
  ∀ i,auxiliaryPairing (rackEquiv g N x i) (rackEquiv g N y i)=(L i)ᵀ*L i

/-- Exact image kernels are a single finite auxiliary experiment. The
identity has no truncation parameter and no kernel tail. -/
theorem auxiliary_network_kernel (L : ∀ i,Mat (H i) (Port g i))
    (hL : ∀ i,Surjective (L i).mulVec) (x : Rack I N) :
    ind (∀ i,(Matrix.fromRows (rackEquiv g N x i).1 (rackEquiv g N x i).2).mulVecLin.ker=
      (L i).mulVecLin.ker)=
      bp (∑ i,num (Port g i)*num (H i))*ind (networkRelations g L x)*
        pr unif (auxiliaryNetworkPairing g L x) := by
  classical
  simp_rw [ind_all,auxiliary_pair_kernel _ (hL _)]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,←bp_sum]
  congr 1
  · simp only [networkRelations,ind_all]
  · have he:=mapW_pr unif (rackEquiv g N)
      (fun y=>∀ i,auxiliaryPairing (rackEquiv g N x i) (y i)=(L i)ᵀ*L i)
    rw [unif_equiv] at he
    change _=pr unif (fun y=>∀ i,auxiliaryPairing (rackEquiv g N x i) (rackEquiv g N y i)=(L i)ᵀ*L i)
    rw [←he,uniform_product_law]
    exact (prodW_pr _ _).symm

end
end Lax793645Proofs.Simplifications
