import Lax793645Proofs.Simplifications.QuadraticNetworkSieve
import Lax793645Proofs.Simplifications.QuadraticPatternSum
import Lax793645Proofs.Simplifications.NormalizedGramBatches

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {N : ℕ}

theorem quadratic_pattern_budget_nonneg (ε : ℝ) (hε : 0 ≤ ε) (t : ℕ) :
    0 ≤ quadraticPatternBudget I J N ε t := by
  unfold quadraticPatternBudget
  apply mul_nonneg
  · exact mul_nonneg (by unfold num; positivity) (bp_pos _).le
  exact add_nonneg (mul_nonneg (bp_pos _).le
    (mul_nonneg (pow_nonneg hε _) (bp_pos _).le)) (bp_pos _).le

variable (g : Route (I×J) G) {H : G → Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

theorem quadratic_exact_implies_relation
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) (x : Rack (I×J) N)
    (hx : quadraticExactNetwork g L Q x) : quadraticNetworkRelation g L Q x := by
  intro i
  refine ⟨?_,(hx i).2⟩
  have hh : (L i).mulVecLin.ker ≤
      (rackEquiv g N x i).1.mulVecLin.ker⊓(rackEquiv g N x i).2.mulVecLin.ker := by
    rw [←stack_matrix_kernel,(hx i).1]
  exact ⟨hh.trans inf_le_left,hh.trans inf_le_right⟩

theorem quadratic_network_relation_pos
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N) :
    0 < pr unif (quadraticNetworkRelation (N:=N) g L Q) :=
  (quadratic_network_exact_pos g L Q hL hN).trans_le
    (pr_mono unif_law.nz (quadratic_exact_implies_relation g L Q))

/-- Normalize the signed Fourier expansion only. The independent
image-kernel error is deliberately excluded from this normalization. -/
theorem quadratic_normalized_sieve_bound
    (P : J → J → Prop) [DecidableRel P] (hP : ∀ u v,P u v → P v u)
    (hmask : ∀ v∈crowded g,P v.1.2 v.2.2)
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N)
    (f : I → Wgt (Rack J N)) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ i x,|f i x| ≤ 1)
    (hf : ∀ (A : Mat J J),Aᵀ=A → (∀ u v,¬P u v → A u v=0) → ∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ| ≤ ε)
    (d t : ℕ) (hrank : peakExpense I J 1 ≤ (N:ℝ)/2) :
    |avg (unifOn (quadraticNetworkRelation g L Q))
      (fun x=>(∏ i,f i (led i x))*quadraticNetworkSieve g H d x)| ≤
      (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-num (H i)))*
        quadraticPatternBudget I J N ε t*(∏ i,singleKernelSieveCost (H i) d) := by
  classical
  let Z:=geoMatrix g (quotientGramData g L Q)
  let w (x : KeyCoordinates (I×J) N):=
    quadraticNetworkSieve g H d (rackCoordinates (I×J) N x)*
      ind (networkRelations g L (rackCoordinates (I×J) N x))
  let K:=quadraticPatternBudget I J N ε t
  let W:=∏ i,singleKernelSieveCost (H i) d
  let z:=pr unif (quadraticNetworkRelation (N:=N) g L Q)
  have hz : 0 < z:=quadratic_network_relation_pos g L Q hL hN
  have hK : 0 ≤ K:=quadratic_pattern_budget_nonneg ε hε t
  have hW : 0 ≤ W:=Finset.prod_nonneg (fun i _=>(single_sieve_cost_ge_one (R:=H i) d).trans' (by norm_num))
  have hh:=quadratic_pattern_sum P hP (crowded g) hmask Z f ε hε hb hf w t hrank
  have hn:=quadratic_network_sieve_fourier_norm (N:=N) g L d
  have hbound : |avg unif (fun x=>(∏ i,f i (led i x))*quadraticNetworkSieve g H d x*
      ind (quadraticNetworkRelation g L Q x))| ≤ bp (-(dim (symmetricRail (crowded g)):ℝ))*K*W := by
    have he x : (∏ i,f i (led i x))*quadraticNetworkSieve g H d x*
        ind (quadraticNetworkRelation g L Q x)=
      (∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*
        ind (quadraticTraced (crowded g) Z ((rackCoordinates (I×J) N).symm x)) := by
      rw [quadratic_relation_network_test,ind_and]
      dsimp only [w,Z]
      rw [LinearEquiv.apply_symm_apply]
      ring
    simp_rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_left hn (mul_nonneg (bp_pos _).le hK))
  rw [←on_unif,avg_condition_formula,abs_div,abs_of_pos hz]
  have he : bp (-(dim (symmetricRail (crowded g)):ℝ))/z ≤
      (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-num (H i))) := by
    refine (div_le_div₀ (bp_pos _).le le_rfl (quadratic_network_exact_pos g L Q hL hN)
      (pr_mono unif_law.nz (quadratic_exact_implies_relation g L Q))).trans
        (quadratic_network_expansion_cost g L Q hL hN)
  calc
    _ ≤ bp (-(dim (symmetricRail (crowded g)):ℝ))*K*W/z := div_le_div_of_nonneg_right hbound hz.le
    _ = (bp (-(dim (symmetricRail (crowded g)):ℝ))/z)*K*W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hK) hW

/-- A finite one-frame estimate with the exact quadratic Gram law,
nominal dependencies, both rank regimes, and physical injectivity. -/
theorem quadratic_dependent_batch_bound
    (P : J → J → Prop) [DecidableRel P] (hP : ∀ u v,P u v → P v u)
    (hmask : ∀ v∈crowded g,P v.1.2 v.2.2)
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N)
    (f : I → Wgt (Rack J N)) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ i x,|f i x| ≤ 1)
    (hf : ∀ (A : Mat J J),Aᵀ=A → (∀ u v,¬P u v → A u v=0) → ∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ| ≤ ε)
    (d t : ℕ) (hrank : peakExpense I J 1 ≤ (N:ℝ)/2)
    (B : ℝ) (hB : 1 ≤ B) (hc : ∀ i,singleKernelSieveCost (H i) d ≤ B) :
    |avg (unifOn (quadraticExactNetwork g L Q)) (fun x=>∏ i,f i (led i x))| ≤
      (8:ℝ)^Fintype.card G*
        ((4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-num (H i)))*
          quadraticPatternBudget I J N ε t*(∏ i,singleKernelSieveCost (H i) d)+
         B^Fintype.card G*∑ i,16*(d+2)*bp ((num (H i)+2)*d+
           ((d:ℝ)+1)*(4*num (H i)-N))) := by
  have hprod x : |∏ i,f i (led i x)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>hb i _)).trans_eq (by simp)
  exact (quadratic_network_sieve_comparison g L Q hL hN _ hprod d B hB hc).trans
    (mul_le_mul_of_nonneg_left (add_le_add
      (quadratic_normalized_sieve_bound g P hP hmask L Q hL hN f ε hε hb hf d t hrank) le_rfl)
        (pow_nonneg (by norm_num) _))

end
end Lax793645Proofs.Simplifications
