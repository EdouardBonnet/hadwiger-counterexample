import Lax793645Proofs.Simplifications.QuadraticProductSieve
import Lax793645Proofs.Simplifications.QuadraticNetworkNormalization
import Lax793645Proofs.Simplifications.NetworkSieveLaw

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] {N : ℕ}
variable (g : Route I G) {H : G → Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

def quadraticNetworkRelation (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (x : Rack I N) : Prop:=∀ i,quadraticRelation (L i) (Q i) (rackEquiv g N x i)

def quadraticNetworkKernels (L : ∀ i,Mat (H i) (Port g i)) (x : Rack I N) : Prop:=
  ∀ i,(stackMatrixEquiv N (rackEquiv g N x i)).mulVecLin.ker=(L i).mulVecLin.ker

def quadraticNetworkSieve (H : G → Type) [∀ i,Fintype (H i)] (d : ℕ) (x : Rack I N) : ℝ:=
  ∏ i,relativeQuadraticSieve (H i) d (rackEquiv g N x i)

theorem quadratic_relation_network_split
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) :
    mapW (unifOn (quadraticNetworkRelation (N:=N) g L Q)) (rackEquiv g N)=
      quadraticRelationProduct L Q := by
  exact (on_equiv (rackEquiv g N)
    (fun x : Network g N=>∀ i,quadraticRelation (L i) (Q i) (x i))).trans
      (uniform_pi_event (fun i (z : Rack (Port g i) N)=>quadraticRelation (L i) (Q i) z))

theorem quadratic_relation_network_test
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) (x : Rack I N) :
    quadraticNetworkRelation g L Q x ↔ networkRelations g L x ∧
      quadraticTraced (crowded g) (geoMatrix g (quotientGramData g L Q))
        ((rackCoordinates I N).symm x) := by
  rw [quadratic_network_traced]
  simp only [quadraticNetworkRelation,networkRelations,quadraticRelation,quotientGramData,forall_and]

theorem quadratic_relation_condition_exact
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) :
    onW (unifOn (quadraticNetworkRelation (N:=N) g L Q)) (quadraticNetworkKernels g L)=
      unifOn (quadraticExactNetwork g L Q) := by
  rw [unifOn_and]
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨hr,hk⟩ i
    exact ⟨hk i,(hr i).2⟩
  · intro h
    constructor
    · intro i
      refine ⟨?_,(h i).2⟩
      have hh : (L i).mulVecLin.ker ≤
          (rackEquiv g N x i).1.mulVecLin.ker⊓(rackEquiv g N x i).2.mulVecLin.ker := by
        rw [←stack_matrix_kernel,(h i).1]
      exact ⟨hh.trans inf_le_left,hh.trans inf_le_right⟩
    · intro i
      exact (h i).1

/-- The physical-frame sieve comparison, in the original tuple-key
coordinates used by the Fourier calculation. -/
theorem quadratic_network_sieve_comparison
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N)
    (f : Wgt (Rack I N)) (hf : ∀ x,|f x| ≤ 1)
    (d : ℕ) (B : ℝ) (hB : 1 ≤ B) (hc : ∀ i,singleKernelSieveCost (H i) d ≤ B) :
    |avg (unifOn (quadraticExactNetwork g L Q)) f| ≤ (8:ℝ)^Fintype.card G*
      (|avg (unifOn (quadraticNetworkRelation g L Q))
        (fun x=>f x*quadraticNetworkSieve g H d x)|+
       B^Fintype.card G*∑ i,16*(d+2)*bp ((num (H i)+2)*d+
         ((d:ℝ)+1)*(4*num (H i)-N))) := by
  let E:=rackEquiv g N
  let μ:=unifOn (quadraticNetworkRelation (N:=N) g L Q)
  let ok (x : Network g N):=∀ i,(stackMatrixEquiv N (x i)).mulVecLin.ker=(L i).mulVecLin.ker
  have he : mapW (unifOn (quadraticExactNetwork g L Q)) E=
      onW (quadraticRelationProduct L Q) ok := by
    rw [←quadratic_relation_condition_exact]
    change mapW (onW μ (ok∘E)) E=_
    rw [map_condition,quadratic_relation_network_split]
  have ha:=mapW_avg (unifOn (quadraticExactNetwork g L Q)) E (fun x=>f (E.symm x))
  rw [he] at ha
  simp only [Equiv.symm_apply_apply] at ha
  have hb:=mapW_avg μ E (fun x=>f (E.symm x)*∏ i,relativeQuadraticSieve (H i) d (x i))
  rw [quadratic_relation_network_split] at hb
  simp only [Equiv.symm_apply_apply] at hb
  have hh:=quadratic_product_conditioned_sieve L Q hL hN
    (fun x=>f (E.symm x)) (fun x=>hf _) d B hB hc
  rw [ha,hb] at hh
  exact hh

def portPhysical (i : G) : KeyCoordinates I N →ₗ[F] Mat (HyperbolicIdx N) (Port g i) where
  toFun x:=stackMatrixEquiv N (rackEquiv g N (rackCoordinates I N x) i)
  map_add' _ _:=by ext a j; cases a <;> rfl
  map_smul' _ _:=by ext a j; cases a <;> rfl

theorem quadratic_network_sieve_fourier_norm
    (L : ∀ i,Mat (H i) (Port g i)) (d : ℕ) :
    fourierNorm (fun x : KeyCoordinates I N=>quadraticNetworkSieve g H d (rackCoordinates I N x)*
      ind (networkRelations g L (rackCoordinates I N x))) ≤ ∏ i,singleKernelSieveCost (H i) d := by
  refine (fourier_norm_mul _ _).trans ?_
  rw [network_relations_fourier_norm,mul_one]
  simp only [quadraticNetworkSieve,relativeQuadraticSieve]
  let v (i : G) (x : KeyCoordinates I N):=kernelSieve d
    (bp (num (H i)-num (Port g i))*binaryKernelCount (portPhysical (N:=N) g i x))
  have he : (fun x : KeyCoordinates I N=>∏ i,kernelSieve d
      (bp (num (H i)-num (Port g i))*binaryKernelCount
        (stackMatrixEquiv N (rackEquiv g N (rackCoordinates I N x) i))))=
      (fun x=>∏ i,v i x) := rfl
  rw [he]
  refine (fourier_norm_product v).trans ?_
  apply Finset.prod_le_prod (fun _ _=>fourier_norm_nonneg _)
  intro i _
  exact relative_quadratic_sieve_fourier_norm (R:=H i) (portPhysical (N:=N) g i) d

end
end Lax793645Proofs.Simplifications
