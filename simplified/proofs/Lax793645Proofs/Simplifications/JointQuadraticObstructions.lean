import Lax793645Proofs.Simplifications.JointQuadraticSpace

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ} {I : Bool→Type}
  [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

theorem joint_quadratic_obstruction_test
    (l : ∀ i,I i→Tag p.g) (s : ∀ i,I i→Label p.b) (z : ∀ i,I i→Base p.g n)
    (hz : ∀ i j,allows (l i j) (z i j))
    (U : Bool→Space (Vec (SelIdx p.b p.j))) (V : Bool→Space (Vec (AIdx p.g n)))
    (hs : ∀ i,LinearIndependent F ((U i).mkQ∘fun j=>selV p.j (s i j)))
    (ht : ∀ i,LinearIndependent F ((V i).mkQ∘fun j=>baseV (z i j)))
    (P : Bool→Comp p.g→Space (Ray p n)) (K : Comp p.g→Space (JointRay p n))
    (hPL : ∀ i e,P i e≤tensorCross (U i) (V i))
    (hK : ∀ e,K e≤jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))
    (hKP : ∀ e i,Disjoint (K e) ((P i e).map (jointInjection i)))
    (R : ℕ)
    (hR : ∀ e,2*dim (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))≤R)
    (hP : ∀ i e,∀ v∈P i e,Matrix.rank (flattenMatrix.symm v)≤R^2+Fintype.card (I i)→
      v∈tensorRectangle (U i) (V i))
    (G : JointProfile p n→ₗ[F]F)
    (ha : ∀ i j,G (jointEndpointMap i (atom p (l i j) (s i j) (z i j)))=0)
    (hp : ∀ y∈jointXspace,(∀ e,y e∈quadraticSquares (jointSpace (fun i=>P i e)))→G y=0)
    (x : JointProfile p n) (hx : x∈jointXspace)
    (hquad : x∈jointQuadraticConstraints
      (fun e=>jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)) K) : G x=0 := by
  classical
  obtain ⟨v,hv,rfl⟩:=(joint_xspace_mem x).mp hx
  obtain ⟨c,y,hvy,hy,hyq,_⟩:=joint_quadratic_cut_annihilator l s z hz U V hs ht P K
    hPL hK hKP R hR hP v hv ((joint_quadratic_constraints_mem _ _ _).mp hquad)
  have he : v=(fun i=>∑ j,c i j•atom p (l i j) (s i j) (z i j))+y:=funext hvy
  change G (jointCutMap v)=0
  rw [he,map_add,map_add]
  have hy0 : G (jointCutMap y)=0:=hp _ (joint_cut_in_space y hy) hyq
  rw [hy0,add_zero]
  change G (jointCutEmbed (fun i=>∑ j,c i j•atom p (l i j) (s i j) (z i j)))=0
  rw [joint_cut_endpoint_sum,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul,map_smul,ha,smul_zero]

end
end Lax793645Proofs.Simplifications
