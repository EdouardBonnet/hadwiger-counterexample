import Lax793645Proofs.Simplifications.NetworkSieveLaw
import Lax793645Proofs.Simplifications.CornerPatternSum

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {N : ℕ}

/-- Explicit finite cost of summing low- and high-cross-rank Gram patterns. -/
def gramRankSum (I J : Type) [Fintype I] [Fintype J] (N : ℕ) (ε : ℝ) (t : ℕ) : ℝ :=
  (num (I×J)+1)*bp (num I*num J*num J)*
    (bp (peakExpense I J t)*(ε^Fintype.card I*bp ((N:ℝ)*blockCompletionCost J*t))+
      bp ((peakExpense I J 1-(N:ℝ)/2)*t))

omit [DecidableEq I] [DecidableEq J] in
theorem gram_rank_sum_nonneg (ε : ℝ) (hε : 0≤ε) (t : ℕ) :
    0≤gramRankSum I J N ε t := by
  unfold gramRankSum
  apply mul_nonneg
  · apply mul_nonneg
    · unfold num; positivity
    · exact (bp_pos _).le
  exact add_nonneg (mul_nonneg (bp_pos _).le
    (mul_nonneg (pow_nonneg hε _) (bp_pos _).le)) (bp_pos _).le

theorem avg_condition_formula {A : Type} [Fintype A] (μ : Wgt A) (p : A→Prop) (f : Wgt A) :
    avg (onW μ p) f=avg μ (fun x=>f x*ind (p x))/pr μ p := by
  unfold onW
  rw [avg_norm,subW_tot]
  congr 1
  unfold avg subW
  apply Finset.sum_congr rfl
  intro x _
  ring

variable (g : Route (I×J) G) {H : G→Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

omit [DecidableEq I] [DecidableEq J] [Fintype G] [∀ i,DecidableEq (H i)] in
theorem exact_network_implies_relation
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i)) (x : Rack (I×J) N)
    (hx : exactNetworkPart g L Q x) : networkRelationPart g L Q x := by
  intro i
  exact ⟨⟨(hx i).1.ge,(hx i).2.1.ge⟩,(hx i).2.2⟩

theorem network_relation_mass_pos
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hroom : ∀ i,2*num (H i)-(N:ℝ)≤-1) :
    0<pr unif (networkRelationPart (N:=N) g L Q) :=
  (network_exact_mass_pos g L Q hL hroom).trans_le
    (pr_mono unif_law.nz (exact_network_implies_relation g L Q))

/-- The full normalized Gram-and-relation estimate. The polynomial tail
is deliberately kept separate, so this normalization never multiplies it. -/
theorem normalized_sieve_gram_bound
    (P : J→J→Prop) [DecidableRel P]
    (hmask : ∀ v∈crowded g,P v.1.2 v.2.2)
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hroom : ∀ i,2*num (H i)-(N:ℝ)≤-1)
    (f : I→Wgt (Rack J N)) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ (A : Mat J J),(∀ u v,¬P u v→A u v=0)→∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤ε)
    (d t : ℕ) (hrank : peakExpense I J 1≤(N:ℝ)/2) :
    |avg (unifOn (networkRelationPart g L Q)) (fun x=>(∏ i,f i (led i x))*networkSieve g H d x)|≤
      (4:ℝ)^Fintype.card G*bp ((N:ℝ)*∑ i,2*(num (Port g i)-num (H i)))*
        gramRankSum I J N ε t*(∏ i,kernelSieveCost (H i) (H i) d) := by
  classical
  let Z:=quotientGramData g L Q
  let w (x : KeyCoordinates (I×J) N):=
    networkSieve g H d (rackCoordinates (I×J) N x)*
      ind (networkRelations g L (rackCoordinates (I×J) N x))
  let K:=gramRankSum I J N ε t
  let W:=∏ i,kernelSieveCost (H i) (H i) d
  let z:=pr unif (networkRelationPart (N:=N) g L Q)
  have hz : 0<z:=network_relation_mass_pos g L Q hL hroom
  have hK : 0≤K:=gram_rank_sum_nonneg ε hε t
  have hW : 0≤W:=Finset.prod_nonneg (fun i _=>(sieve_cost_ge_one (R:=H i) d).trans' (by norm_num))
  have hh:=gram_pattern_sum P (crowded g) hmask (directions g Z) f ε hε hb hf w t hrank
  change |avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*
    ind (traced x (crowded g) (directions g Z)))|≤bp (-((crowded g).card:ℝ))*K*fourierNorm w at hh
  have hn:=network_sieve_fourier_norm (N:=N) g L d
  have hbound : |avg unif (fun x=>(∏ i,f i (led i x))*networkSieve g H d x*
      ind (networkRelationPart g L Q x))|≤bp (-netSize g)*K*W := by
    have he x : (∏ i,f i (led i x))*networkSieve g H d x*ind (networkRelationPart g L Q x)=
      (∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*
        ind (traced x (crowded g) (directions g Z)) := by
      rw [relation_network_test,ind_and,match_crowd]
      dsimp only [w,Z]
      rw [LinearEquiv.apply_symm_apply]
      ring
    simp_rw [he]
    refine hh.trans ?_
    rw [rail_count]
    exact mul_le_mul_of_nonneg_left hn (mul_nonneg (bp_pos _).le hK)
  rw [←on_unif,avg_condition_formula,abs_div,abs_of_pos hz]
  have he : bp (-netSize g)/z≤(4:ℝ)^Fintype.card G*
      bp ((N:ℝ)*∑ i,2*(num (Port g i)-num (H i))) := by
    refine (div_le_div₀ (bp_pos _).le le_rfl (network_exact_mass_pos g L Q hL hroom)
      (pr_mono unif_law.nz (exact_network_implies_relation g L Q))).trans
        (network_gram_expansion_cost g L Q hL hroom)
  calc
    _≤bp (-netSize g)*K*W/z := div_le_div_of_nonneg_right hbound hz.le
    _=(bp (-netSize g)/z)*K*W := by ring
    _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hK) hW

/-- A finite conditional-frame estimate containing both rank regimes,
nominal-deficiency normalization, and the simultaneous image-kernel tail. -/
theorem dependent_gram_batch_bound
    (P : J→J→Prop) [DecidableRel P]
    (hmask : ∀ v∈crowded g,P v.1.2 v.2.2)
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hroom : ∀ i,2*num (H i)-(N:ℝ)≤-1)
    (f : I→Wgt (Rack J N)) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ (A : Mat J J),(∀ u v,¬P u v→A u v=0)→∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤ε)
    (d t : ℕ) (hrank : peakExpense I J 1≤(N:ℝ)/2)
    (B : ℝ) (hB : 1≤B) (hc : ∀ i,kernelSieveCost (H i) (H i) d≤B) :
    |avg (unifOn (exactNetworkPart g L Q)) (fun x=>∏ i,f i (led i x))|≤
      (8:ℝ)^Fintype.card G*
        ((4:ℝ)^Fintype.card G*bp ((N:ℝ)*∑ i,2*(num (Port g i)-num (H i)))*
          gramRankSum I J N ε t*(∏ i,kernelSieveCost (H i) (H i) d)+
         B^Fintype.card G*∑ i,16*(d+2)*bp ((2*num (H i)+4)*d+
           ((d:ℝ)+1)*(4*num (H i)-(N:ℝ)))) := by
  have hprod x : |∏ i,f i (led i x)|≤1 := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>hb i _)).trans_eq (by simp)
  exact (network_sieve_comparison g L Q hL hroom _ hprod d B hB hc).trans
    (mul_le_mul_of_nonneg_left (add_le_add
      (normalized_sieve_gram_bound g P hmask L Q hL hroom f ε hε hb hf d t hrank) le_rfl)
        (pow_nonneg (by norm_num) _))

end
end Lax793645Proofs.Simplifications
