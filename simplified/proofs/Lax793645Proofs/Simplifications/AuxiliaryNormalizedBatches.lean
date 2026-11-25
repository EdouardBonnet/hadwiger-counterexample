import Lax793645Proofs.Simplifications.AuxiliaryNetworkExpansion
import Lax793645Proofs.Simplifications.QuadraticStatusFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {N : ℕ}

def auxiliarySlotOrder (I J : Type) : (Bool×(I×J))≃(I×(Bool×J)) where
  toFun c:=(c.2.1,(c.1,c.2.2))
  invFun c:=(c.2.1,(c.1,c.2.2))
  left_inv _:=rfl
  right_inv _:=rfl

def auxiliaryBatchRack (I J : Type) (N : ℕ) :
    (Rack (I×J) N×Rack (I×J) N)≃Rack (I×(Bool×J)) N where
  toFun z:=((fun u c=>if c.2.1 then z.2.1 u (c.1,c.2.2) else z.1.1 u (c.1,c.2.2)),
    fun u c=>if c.2.1 then z.2.2 u (c.1,c.2.2) else z.1.2 u (c.1,c.2.2))
  invFun z:=((fun u c=>z.1 u (c.1,(false,c.2)),fun u c=>z.2 u (c.1,(false,c.2))),
    (fun u c=>z.1 u (c.1,(true,c.2)),fun u c=>z.2 u (c.1,(true,c.2))))
  left_inv z:=rfl
  right_inv z:=by
    apply Prod.ext <;> ext u ⟨i,b,j⟩ <;> cases b <;> rfl

def auxiliaryOriginal : KeyCoordinates (I×(Bool×J)) N→ₗ[F]KeyCoordinates (I×J) N where
  toFun z c:=z (c.1,(c.2.1,(c.2.2.1,(false,c.2.2.2))))
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem auxiliary_batch_coordinates (x y : Rack (I×J) N) :
    (rackCoordinates (I×(Bool×J)) N).symm (auxiliaryBatchRack I J N (x,y))=
      keyReindex (auxiliarySlotOrder I J) N
        (auxiliaryCoordinates (I×J) N ((rackCoordinates (I×J) N).symm x,(rackCoordinates (I×J) N).symm y)):=by
  funext ⟨u,b,i,a,j⟩
  cases b <;> cases a <;> rfl

variable (g : Route (I×J) G) {H : G→Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

/-- Direct batches with exact kernels, certified by auxiliary dual
vectors. There is no image-kernel cutoff or remainder term. -/
theorem auxiliary_normalized_batch_bound
    (E : Rail J) (hE : ∀ u v,(u,v)∈E→(v,u)∈E)
    (hmask : ∀ v∈crowded g,(v.1.2,v.2.2)∈E)
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2≤N)
    (f : I→Wgt (Rack J N)) (δ : ℝ) (hδ : 0≤δ)
    (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ A : Mat J J,Aᵀ=A→withinRail A E→∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤δ)
    (t : ℕ) (hroom : peakExpense I (Bool×J) 1≤(N:ℝ)/2) :
    |avg (unifOn (quadraticExactNetwork g L Q)) (fun x=>∏ i,f i (led i x))|≤
      (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-num (H i)))*
        quadraticPatternBudget I (Bool×J) N (δ+bp (-(N:ℝ)/2)) t:=by
  classical
  let e:=auxiliarySlotOrder I J
  let E':=railReindex e (auxiliaryRail (crowded g))
  let Z:=auxiliaryTarget (geoMatrix g (quotientGramData g L Q)) (geoMatrix g (fun i=>(L i)ᵀ*L i))
  let P (u v : Bool×J):=(u.2,v.2)∈E ∧ (u.1=false ∨ v.1=false)
  let F i (x : Rack (Bool×J) N):=f i (led false x)
  let w (z : KeyCoordinates (I×(Bool×J)) N):=
    ind (networkRelations g L (rackCoordinates (I×J) N (auxiliaryOriginal z)))
  let K:=quadraticPatternBudget I (Bool×J) N (δ+bp (-(N:ℝ)/2)) t
  have hK : 0≤K:=quadratic_pattern_budget_nonneg _ (add_nonneg hδ (bp_pos _).le) t
  have hP u v : P u v→P v u:=fun h=>⟨hE _ _ h.1,h.2.symm⟩
  have hE' : ∀ v∈E',P v.1.2 v.2.2:=by
    intro v hv
    have hh:= (mem_rail_reindex e (auxiliaryRail (crowded g)) v.1 v.2).mp hv
    have hh':=((mem_filter.mp hh).2)
    exact ⟨hmask _ hh'.1,hh'.2⟩
  have hlocal (A : Mat (Bool×J) (Bool×J)) (hA : Aᵀ=A)
      (hm : ∀ u v,¬P u v→A u v=0) (i : I) (ξ : KeyCoordinates (Bool×J) N) :
      |linearFourier (fun z=>phasedBy A (rackCoordinates (Bool×J) N z)*F i (rackCoordinates (Bool×J) N z)) ξ|≤
        δ+bp (-(N:ℝ)/2):=by
    have haux : auxiliaryBlock A true true=0:=by
      ext u v
      exact hm (true,u) (true,v) (by simp [P])
    have ha : withinRail (auxiliaryBlock A false false) E:=by
      intro u v huv
      exact hm (false,u) (false,v) (fun h=>huv h.1)
    have hh:=auxiliary_batch_fourier E (fun z=>f i (rackCoordinates J N z)) δ hδ
      (fun z=>hb i _) (fun B hB hBE ξ=>hf B hB hBE i ξ) A hA ha haux ξ
    exact hh
  have hw : fourierNorm w≤1:=by
    have hh:=fourier_norm_affine_map (auxiliaryOriginal (I:=I) (J:=J) (N:=N)) 0
      (fun z=>ind (networkRelations g L (rackCoordinates (I×J) N z)))
    simpa only [add_zero,network_relations_fourier_norm,w] using hh
  have hh:=quadratic_pattern_sum P hP E' hE' (matrixReindex e Z) F
    (δ+bp (-(N:ℝ)/2)) (add_nonneg hδ (bp_pos _).le) (fun i z=>hb i _)
    hlocal w t hroom
  have hbound : |avg unif (fun x=>avg unif (fun y=>(∏ i,f i (led i x))*
      ind (networkRelations g L x)*ind (quadraticTraced (auxiliaryRail (crowded g)) Z
        (auxiliaryCoordinates (I×J) N ((rackCoordinates (I×J) N).symm x,(rackCoordinates (I×J) N).symm y)))))|≤
      bp (-(dim (symmetricRail (auxiliaryRail (crowded g))):ℝ))*K:=by
    have hav:=mapW_avg unif (auxiliaryBatchRack I J N)
      (fun z=>(∏ i,F i (led i z))*w ((rackCoordinates (I×(Bool×J)) N).symm z)*
        ind (quadraticTraced E' (matrixReindex e Z) ((rackCoordinates (I×(Bool×J)) N).symm z)))
    rw [unif_equiv] at hav
    rw [show (unif : Wgt (Rack (I×J) N×Rack (I×J) N))=pairW unif unif from pair_unif,
      pairW_avg] at hav
    have hv (x y : Rack (I×J) N) :
        (∏ i,F i (led i (auxiliaryBatchRack I J N (x,y))))*
          w ((rackCoordinates (I×(Bool×J)) N).symm (auxiliaryBatchRack I J N (x,y)))*
          ind (quadraticTraced E' (matrixReindex e Z)
            ((rackCoordinates (I×(Bool×J)) N).symm (auxiliaryBatchRack I J N (x,y))))=
        (∏ i,f i (led i x))*ind (networkRelations g L x)*
          ind (quadraticTraced (auxiliaryRail (crowded g)) Z
            (auxiliaryCoordinates (I×J) N ((rackCoordinates (I×J) N).symm x,(rackCoordinates (I×J) N).symm y))):=by
      have htrace:=quadratic_traced_reindex e (auxiliaryRail (crowded g)) Z
        (auxiliaryCoordinates (I×J) N ((rackCoordinates (I×J) N).symm x,(rackCoordinates (I×J) N).symm y))
      have hcoords:=auxiliary_batch_coordinates x y
      have ho : rackCoordinates (I×J) N (auxiliaryOriginal
          ((rackCoordinates (I×(Bool×J)) N).symm (auxiliaryBatchRack I J N (x,y))))=x:=rfl
      dsimp only [w]
      rw [ho,hcoords,htrace]
      rfl
    simp_rw [hv] at hav
    rw [←hav]
    have hd : dim (symmetricRail E')=dim (symmetricRail (auxiliaryRail (crowded g))):=
      symmetric_rail_reindex_dimension e _
    exact hh.trans (by rw [hd]; simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hw (mul_nonneg (bp_pos _).le hK))
  have hz:=quadratic_network_exact_pos (N:=N) g L Q hL hN
  rw [←on_unif,avg_condition_formula,auxiliary_network_expansion g L Q hL,
    abs_div,abs_mul,abs_of_pos (bp_pos _),abs_of_pos hz]
  calc
    _≤bp (∑ i,num (Port g i)*num (H i))*
      (bp (-(dim (symmetricRail (auxiliaryRail (crowded g))):ℝ))*K)/
        pr unif (quadraticExactNetwork g L Q):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (bp_pos _).le) hz.le
    _=(bp (∑ i,num (Port g i)*num (H i))*
      bp (-(dim (symmetricRail (auxiliaryRail (crowded g))):ℝ))/
        pr unif (quadraticExactNetwork g L Q))*K:=by ring
    _≤_:=mul_le_mul_of_nonneg_right (auxiliary_network_expansion_cost g L Q hL hN) hK

end
end Lax793645Proofs.Simplifications
