import Lax793645Proofs.Simplifications.QuadraticRailReindex

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] {N : ℕ}
variable (g : Route I G) {H : G→Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

theorem auxiliary_network_trace (L : ∀ i,Mat (H i) (Port g i)) (x y : Rack I N) :
    auxiliaryNetworkPairing g L x y ↔
      railsM (crowded g) (auxiliaryPairing x y)=
        railsM (crowded g) (geoMatrix g (fun i=>(L i)ᵀ*L i)):=by
  constructor
  · intro h
    funext z
    let i : Port g (g z.val.1):=⟨z.val.1,rfl⟩
    let j : Port g (g z.val.1):=⟨z.val.2,(mem_filter.mp z.property).2.symm⟩
    have hh:=congrFun (congrFun (h (g z.val.1)) i) j
    change auxiliaryPairing x y i.val j.val=geoMatrix g _ i.val j.val
    rw [geo_matrix_block]
    exact hh
  · intro h c
    ext i j
    let z : crowded g:=⟨(i.val,j.val),mem_filter.mpr ⟨mem_univ _,i.property.trans j.property.symm⟩⟩
    have hh:=congrFun h z
    change auxiliaryPairing x y i.val j.val=geoMatrix g _ i.val j.val at hh
    rw [geo_matrix_block] at hh
    exact hh

theorem quadratic_exact_network_split (L : ∀ i,Mat (H i) (Port g i))
    (Q : ∀ i,Mat (H i) (H i)) (x : Rack I N) :
    quadraticExactNetwork g L Q x ↔
      (∀ i,(Matrix.fromRows (rackEquiv g N x i).1 (rackEquiv g N x i).2).mulVecLin.ker=
        (L i).mulVecLin.ker) ∧
      quadraticTraced (crowded g) (geoMatrix g (quotientGramData g L Q)) ((rackCoordinates I N).symm x):=by
  rw [quadratic_network_traced]
  exact forall_and

/-- Exact finite replacement of the kernel sieve inside the raw
expectation. Every original query factor is retained. -/
theorem auxiliary_network_expansion (L : ∀ i,Mat (H i) (Port g i))
    (Q : ∀ i,Mat (H i) (H i)) (hL : ∀ i,Surjective (L i).mulVec)
    (f : Wgt (Rack I N)) :
    avg unif (fun x=>f x*ind (quadraticExactNetwork g L Q x))=
      bp (∑ i,num (Port g i)*num (H i))*
      avg unif (fun x=>avg unif (fun y=>f x*ind (networkRelations g L x)*
        ind (quadraticTraced (auxiliaryRail (crowded g))
          (auxiliaryTarget (geoMatrix g (quotientGramData g L Q))
            (geoMatrix g (fun i=>(L i)ᵀ*L i)))
          (auxiliaryCoordinates I N ((rackCoordinates I N).symm x,(rackCoordinates I N).symm y))))) := by
  have hE : ∀ i j,(i,j)∈crowded g→(j,i)∈crowded g:=fun i j h=>
    mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.symm⟩
  have he x y : quadraticTraced (auxiliaryRail (crowded g))
      (auxiliaryTarget (geoMatrix g (quotientGramData g L Q))
        (geoMatrix g (fun i=>(L i)ᵀ*L i)))
      (auxiliaryCoordinates I N ((rackCoordinates I N).symm x,(rackCoordinates I N).symm y)) ↔
      quadraticTraced (crowded g) (geoMatrix g (quotientGramData g L Q)) ((rackCoordinates I N).symm x) ∧
      auxiliaryNetworkPairing g L x y:=by
    rw [auxiliary_trace_iff _ hE,auxiliary_network_trace]
    rfl
  simp_rw [he,ind_and,quadratic_exact_network_split,ind_and,auxiliary_network_kernel g L hL]
  rw [←avg_mul']
  apply avg_congr
  intro x _
  change _=bp _*avg unif (fun y=>f x*ind (networkRelations g L x)*
    (ind (quadraticTraced _ _ _)*ind (auxiliaryNetworkPairing g L x y)))
  simp_rw [←mul_assoc,avg_mul']
  unfold pr
  ring

/-- The auxiliary normalization can only improve the original
deficiency cost: surjectivity gives fewer quotient rows than columns. -/
theorem auxiliary_network_expansion_cost (L : ∀ i,Mat (H i) (Port g i))
    (Q : ∀ i,Mat (H i) (H i)) (hL : ∀ i,Surjective (L i).mulVec)
    (hN : ∀ i,2*num (H i)+2≤N) :
    bp (∑ i,num (Port g i)*num (H i))*
      bp (-(dim (symmetricRail (auxiliaryRail (crowded g))):ℝ))/
        pr unif (quadraticExactNetwork (N:=N) g L Q) ≤
      (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-num (H i))) := by
  have hE : ∀ i j,(i,j)∈crowded g→(j,i)∈crowded g:=fun i j h=>
    mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.symm⟩
  have hr i : num (H i)≤num (Port g i):=by
    have hh:=LinearMap.finrank_le_finrank_of_surjective (f:=(L i).mulVecLin) (hL i)
    change dim (Vec (H i))≤dim (Vec (Port g i)) at hh
    rw [dim_vec,dim_vec] at hh
    exact_mod_cast hh
  have hsum : (∑ i,num (Port g i)*num (H i))≤Fintype.card (crowded g):=by
    rw [Fintype.card_coe,rail_count,netSize]
    exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hr i) (by unfold num; positivity))
  apply (div_le_div_of_nonneg_right ?_ (pr_nonneg unif_law.nz)).trans
    (quadratic_network_expansion_cost g L Q hL hN)
  rw [←bp_add,auxiliary_rail_dimension _ hE,Nat.cast_add]
  apply bp_le
  linarith

end
end Lax793645Proofs.Simplifications
