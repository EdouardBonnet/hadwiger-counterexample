import Lax793645Proofs.Simplifications.SimultaneousKernelSieve
import Lax793645Proofs.Simplifications.NetworkKernelNormalization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] {N : ℕ}
variable (g : Route I G) {H : G→Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

def networkRelationPart (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (x : Rack I N) : Prop :=
  ∀ i,relationGram (L i) (L i) (Q i) (rackEquiv g N x i)

def networkRelations (L : ∀ i,Mat (H i) (Port g i)) (x : Rack I N) : Prop :=
  ∀ i,LinearMap.ker (L i).mulVecLin≤LinearMap.ker (rackEquiv g N x i).1.mulVecLin ∧
    LinearMap.ker (L i).mulVecLin≤LinearMap.ker (rackEquiv g N x i).2.mulVecLin

def networkExactKernels (L : ∀ i,Mat (H i) (Port g i)) (x : Rack I N) : Prop :=
  ∀ i,LinearMap.ker (rackEquiv g N x i).1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
    LinearMap.ker (rackEquiv g N x i).2.mulVecLin=LinearMap.ker (L i).mulVecLin

def quotientGramData (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) : GeoM g :=
  fun i=>(L i)ᵀ*Q i*L i

def networkSieve (H : G→Type) [∀ i,Fintype (H i)] (d : ℕ) (x : Rack I N) : ℝ :=
  ∏ i,relativeKernelSieve (H i) (H i) d (rackEquiv g N x i)

omit [∀ i,DecidableEq (H i)] in
theorem relation_network_split
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) :
    mapW (unifOn (networkRelationPart (N:=N) g L Q)) (rackEquiv g N)=relationProductLaw L Q := by
  exact (on_equiv (rackEquiv g N) (fun x : Network g N=>∀ i,relationGram (L i) (L i) (Q i) (x i))).trans
    (uniform_pi_event (fun i (z : Rack (Port g i) N)=>relationGram (L i) (L i) (Q i) z))

omit [DecidableEq I] [Fintype G] [∀ i,DecidableEq (H i)] in
theorem relation_network_test
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) (x : Rack I N) :
    networkRelationPart g L Q x ↔ networkRelations g L x ∧ gramPart (quotientGramData g L Q) x := by
  simp only [networkRelationPart,networkRelations,relationGram,gramPart,quotientGramData,forall_and]

omit [Fintype G] [∀ i,DecidableEq (H i)] in
theorem relation_condition_exact
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) :
    onW (unifOn (networkRelationPart (N:=N) g L Q)) (networkExactKernels g L)=
      unifOn (exactNetworkPart g L Q) := by
  rw [unifOn_and]
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨hr,hk⟩ i
    exact ⟨(hk i).1,(hk i).2,(hr i).2⟩
  · intro h
    constructor
    · intro i
      exact ⟨⟨(h i).1.ge,(h i).2.1.ge⟩,(h i).2.2⟩
    · intro i
      exact ⟨(h i).1,(h i).2.1⟩

/-- The simultaneous relative-kernel comparison in original rack
coordinates, with every query column still present. -/
theorem network_sieve_comparison
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hroom : ∀ i,2*num (H i)-(N:ℝ)≤-1)
    (f : Wgt (Rack I N)) (hf : ∀ x,|f x|≤1)
    (d : ℕ) (B : ℝ) (hB : 1≤B) (hc : ∀ i,kernelSieveCost (H i) (H i) d≤B) :
    |avg (unifOn (exactNetworkPart g L Q)) f|≤(8:ℝ)^Fintype.card G*
      (|avg (unifOn (networkRelationPart g L Q)) (fun x=>f x*networkSieve g H d x)|+
       B^Fintype.card G*∑ i,16*(d+2)*bp ((2*num (H i)+4)*d+
         ((d:ℝ)+1)*(4*num (H i)-(N:ℝ)))) := by
  let E:=rackEquiv g N
  let μ:=unifOn (networkRelationPart (N:=N) g L Q)
  let ok (x : Network g N):=∀ i,
    LinearMap.ker (x i).1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
    LinearMap.ker (x i).2.mulVecLin=LinearMap.ker (L i).mulVecLin
  have he : mapW (unifOn (exactNetworkPart g L Q)) E=onW (relationProductLaw L Q) ok := by
    rw [←relation_condition_exact]
    change mapW (onW μ (ok ∘ E)) E=_
    rw [map_condition,relation_network_split]
  have ha:=mapW_avg (unifOn (exactNetworkPart g L Q)) E (fun x=>f (E.symm x))
  rw [he] at ha
  simp only [Equiv.symm_apply_apply] at ha
  have hb:=mapW_avg μ E (fun x=>f (E.symm x)*∏ i,relativeKernelSieve (H i) (H i) d (x i))
  rw [relation_network_split] at hb
  simp only [Equiv.symm_apply_apply] at hb
  have hh:=simultaneous_conditioned_sieve (U:=Fin N) L Q hL
    (fun i=>by simpa only [num,Fintype.card_fin] using hroom i)
    (fun x=>f (E.symm x)) (fun x=>hf _) d B hB hc
  rw [ha,hb] at hh
  simpa only [num,Fintype.card_fin,networkSieve] using hh

def portPlus (i : G) : KeyCoordinates I N→ₗ[F] Mat (Fin N) (Port g i) where
  toFun x:=((rackEquiv g N) (rackCoordinates I N x) i).1
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def portMinus (i : G) : KeyCoordinates I N→ₗ[F] Mat (Fin N) (Port g i) where
  toFun x:=((rackEquiv g N) (rackCoordinates I N x) i).2
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

omit [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)] in
theorem network_relations_fourier_norm (L : ∀ i,Mat (H i) (Port g i)) :
    fourierNorm (fun x : KeyCoordinates I N=>ind (networkRelations g L (rackCoordinates I N x)))=1 := by
  have hp i:=kernel_containment_fourier_norm (portPlus (N:=N) g i) (LinearMap.ker (L i).mulVecLin)
  have hm i:=kernel_containment_fourier_norm (portMinus (N:=N) g i) (LinearMap.ker (L i).mulVecLin)
  apply le_antisymm
  · simp only [networkRelations,ind_all,ind_and]
    refine (fourier_norm_product (fun i x=>ind (LinearMap.ker (L i).mulVecLin≤LinearMap.ker (portPlus (N:=N) g i x).mulVecLin)*
      ind (LinearMap.ker (L i).mulVecLin≤LinearMap.ker (portMinus (N:=N) g i x).mulVecLin))).trans ?_
    have h i:=fourier_norm_mul
      (fun x=>ind (LinearMap.ker (L i).mulVecLin≤LinearMap.ker (portPlus (N:=N) g i x).mulVecLin))
      (fun x=>ind (LinearMap.ker (L i).mulVecLin≤LinearMap.ker (portMinus (N:=N) g i x).mulVecLin))
    simp only [hp,hm,mul_one] at h
    exact (Finset.prod_le_prod (fun _ _=>fourier_norm_nonneg _) (fun i _=>h i)).trans_eq (by simp)
  have hh:=fourier_norm_point (fun x : KeyCoordinates I N=>ind (networkRelations g L (rackCoordinates I N x))) 0
  have hz : networkRelations g L (rackCoordinates I N 0) := by
    intro i
    constructor <;> intro v hv <;> change (0 : Mat (Fin N) (Port g i))*ᵥv=0 <;> simp
  simpa only [ind_one hz,abs_one] using hh

omit [∀ i,DecidableEq (H i)] in
/-- Relation indicators cost one in Fourier norm; the remaining cost
comes only from the bounded-degree image-kernel polynomials. -/
theorem network_sieve_fourier_norm (L : ∀ i,Mat (H i) (Port g i)) (d : ℕ) :
    fourierNorm (fun x : KeyCoordinates I N=>networkSieve g H d (rackCoordinates I N x)*
      ind (networkRelations g L (rackCoordinates I N x)))≤∏ i,kernelSieveCost (H i) (H i) d := by
  refine (fourier_norm_mul _ _).trans ?_
  rw [network_relations_fourier_norm,mul_one]
  apply (fourier_norm_product (fun i x=>relativeKernelSieve (H i) (H i) d
    (portPlus (N:=N) g i x,portMinus g i x))).trans
  exact Finset.prod_le_prod (fun _ _=>fourier_norm_nonneg _)
    (fun i _=>relative_sieve_fourier_norm (R:=H i) (S:=H i) (portPlus (N:=N) g i) (portMinus (N:=N) g i) d)

end
end Lax793645Proofs.Simplifications
