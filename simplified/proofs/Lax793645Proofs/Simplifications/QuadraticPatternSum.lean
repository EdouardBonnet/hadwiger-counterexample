import Lax793645Proofs.Simplifications.QuadraticRailSpaces
import Lax793645Proofs.Simplifications.SymmetricLowRankBatches

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {N : ℕ}

def quadraticPatternBudget (I J : Type) [Fintype I] [Fintype J]
    (N : ℕ) (ε : ℝ) (t : ℕ) : ℝ:=
  (num (I×J)+1)*bp (num I*num J*num J)*
    (bp (peakExpense I J t)*(ε^Fintype.card I*bp ((N:ℝ)*symmetricCompletionCost J*t))+
      bp ((peakExpense I J 1-(N:ℝ)/2)*t))

theorem sum_symmetric_rail (E : Rail I) (f : Mat I I → ℝ) :
    (∑ M : symmetricRail E,f M.val)=
      ∑ M : Mat I I,@ite ℝ (M∈symmetricRail E) (Classical.propDecidable _) (f M) 0 := by
  classical
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter (fun M=>M∈symmetricRail E))
    (fun M=>by simp) f).symm

/-- Sum all permitted quadratic Gram characters. Both cross-rank regimes
retain the exact quadratic normalization and every original query batch. -/
theorem quadratic_pattern_sum (P : J → J → Prop) [DecidableRel P]
    (hP : ∀ u v,P u v → P v u)
    (E : Rail (I×J)) (hE : ∀ v∈E,P v.1.2 v.2.2) (Z : Mat (I×J) (I×J))
    (f : I → Wgt (Rack J N)) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ i x,|f i x| ≤ 1)
    (hf : ∀ (A : Mat J J),Aᵀ=A → (∀ u v,¬P u v → A u v=0) → ∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ| ≤ ε)
    (w : Wgt (KeyCoordinates (I×J) N)) (t : ℕ)
    (hroom : peakExpense I J 1 ≤ (N:ℝ)/2) :
    |avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*
      ind (quadraticTraced E Z ((rackCoordinates (I×J) N).symm x)))| ≤
      bp (-(dim (symmetricRail E):ℝ))*quadraticPatternBudget I J N ε t*fourierNorm w := by
  classical
  let F (M : Avenue I J):=if M∈symmetricRail E then
    wsign (mpair M Z)*avg unif (fun x=>phasedBy M x*(∏ i,f i (led i x))*
      w ((rackCoordinates (I×J) N).symm x)) else 0
  let L:=ε^Fintype.card I*bp ((N:ℝ)*symmetricCompletionCost J*t)
  have hmask (M : Avenue I J) (hm : M∈symmetricRail E) : ∀ x y,¬P x.2 y.2 → M x y=0 := by
    intro x y hxy
    exact hm.2 x y (fun h=>hxy (hE (x,y) h))
  have hs M (ht : peak M<t) : |F M| ≤ L*fourierNorm w := by
    by_cases hm : M∈symmetricRail E
    · dsimp only [F]
      rw [if_pos hm,abs_mul,wsign_abs,one_mul]
      refine (symmetric_low_rank_batch_weight P hP M hm.1 (hmask M hm) f ε hε hf w).trans ?_
      have hh : (peak M:ℝ) ≤ t:=by exact_mod_cast ht.le
      apply mul_le_mul_of_nonneg_right _ (fourier_norm_nonneg w)
      exact mul_le_mul_of_nonneg_left (bp_le (mul_le_mul_of_nonneg_left hh
        (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg (symmetricCompletionCost J))))) (pow_nonneg hε _)
    · simp only [F,hm,if_false,abs_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg hε _) (bp_pos _).le) (fourier_norm_nonneg w)
  have hl M (_ht : t ≤ peak M) : |F M| ≤ bp (-((N:ℝ)/2)*peak M)*fourierNorm w := by
    by_cases hm : M∈symmetricRail E
    · dsimp only [F]
      rw [if_pos hm,abs_mul,wsign_abs,one_mul]
      convert high_rank_batch_weight M f hb w using 1
      congr 2
      ring
    · simp only [F,hm,if_false,abs_zero]
      exact mul_nonneg (bp_pos _).le (fourier_norm_nonneg w)
  have hh:=weighted_pattern_sum_bound F t L ((N:ℝ)/2) (fourierNorm w)
    (mul_nonneg (pow_nonneg hε _) (bp_pos _).le) (fourier_norm_nonneg w) hroom hs hl
  have he : avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*
      ind (quadraticTraced E Z ((rackCoordinates (I×J) N).symm x)))=
      bp (-(dim (symmetricRail E):ℝ))*∑ M : Avenue I J,F M := by
    simp_rw [quadratic_rail_expansion,←avg_mul']
    rw [avg_avg]
    have hv (M : symmetricRail E) : avg unif (fun x=>(∏ i,f i (led i x))*
        w ((rackCoordinates (I×J) N).symm x)*
        (wsign (mpair M.val Z)*wsign (gramPrimitive M.val ((rackCoordinates (I×J) N).symm x))))=
        wsign (mpair M.val Z)*avg unif (fun x=>phasedBy M.val x*(∏ i,f i (led i x))*
          w ((rackCoordinates (I×J) N).symm x)) := by
      rw [←avg_mul']
      apply avg_congr
      intro x _
      have hp : wsign (gramPrimitive M.val ((rackCoordinates (I×J) N).symm x))=phasedBy M.val x:=rfl
      rw [hp]
      ring
    simp_rw [hv]
    have hu (v : Wgt (symmetricRail E)) : avg unif v=
        bp (-(dim (symmetricRail E):ℝ))*∑ M,v M := by
      unfold avg
      simp only [unif_apply,card_space,←bp_neg,←Finset.mul_sum]
    rw [hu]
    congr 1
    simpa only [F] using sum_symmetric_rail E (fun M=>wsign (mpair M Z)*
      avg unif (fun x=>phasedBy M x*(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)))
  rw [he,abs_mul,abs_of_pos (bp_pos _)]
  exact (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq (mul_assoc _ _ _).symm

end
end Lax793645Proofs.Simplifications
