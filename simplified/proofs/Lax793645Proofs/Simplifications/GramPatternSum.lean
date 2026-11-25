import Lax793645Proofs.Simplifications.LowRankBatchWeights
import Lax793645Proofs.Simplifications.CrossPatternSums

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {N : ℕ}

theorem sum_ledger (E : Rail I) (f : Mat I I→ℝ) :
    (∑ v:Vec E,f (ledgerM E v))=∑ M:Mat I I,@ite ℝ (withinRail M E) (Classical.propDecidable _) (f M) 0 := by
  classical
  rw [←Finset.sum_filter]
  apply Finset.sum_nbij' (ledgerM E) (railsM E)
  · intro v _
    exact mem_filter.mpr ⟨mem_univ _,within_recorded E v⟩
  · intro M _
    exact mem_univ _
  · intro v _
    exact inLedger E v
  · intro M h
    exact ledger_recovers E M (mem_filter.mp h).2
  · intro v _
    rfl

/-- A common nonnegative weight may be factored out of both rank regimes. -/
theorem weighted_pattern_sum_bound (f : Avenue I J→ℝ) (t : ℕ) (L α W : ℝ)
    (hL : 0≤L) (hW : 0≤W) (hα : peakExpense I J 1≤α)
    (hsmall : ∀ M,peak M<t→|f M|≤L*W)
    (hlarge : ∀ M,t≤peak M→|f M|≤bp (-α*peak M)*W) :
    |∑ M: Avenue I J,f M|≤
      ((num (I×J)+1)*bp (num I*num J*num J)*
        (bp (peakExpense I J t)*L+bp ((peakExpense I J 1-α)*t)))*W := by
  by_cases h0 : W=0
  · subst W
    have hz M : f M=0 := by
      have h : |f M|≤0 := by
        by_cases ht : peak M<t
        · simpa using hsmall M ht
        · simpa using hlarge M (Nat.le_of_not_gt ht)
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simp only [hz,Finset.sum_const_zero,abs_zero,mul_zero,le_refl]
  have hpos : 0<W := lt_of_le_of_ne hW (Ne.symm h0)
  have hs M (h : peak M<t) : |f M/W|≤L := by
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (hsmall M h)
  have hl M (h : t≤peak M) : |f M/W|≤bp (-α*peak M) := by
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (hlarge M h)
  have hh := full_pattern_sum_bound (fun M=>f M/W) t L α hL hα hs hl
  rw [←Finset.sum_div,abs_div,abs_of_pos hpos] at hh
  exact (div_le_iff₀ hpos).mp hh

/-- All low- and high-rank Gram patterns, including their normalization. -/
theorem gram_pattern_sum (P : J→J→Prop) [DecidableRel P]
    (E : Rail (I×J)) (hE : ∀ v∈E,P v.1.2 v.2.2) (Z : Vec E)
    (f : I→Wgt (Rack J N)) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ (A : Mat J J),(∀ u v,¬P u v→A u v=0)→∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤ε)
    (w : Wgt (KeyCoordinates (I×J) N)) (t : ℕ)
    (hroom : peakExpense I J 1≤(N:ℝ)/2) :
    |avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*ind (traced x E Z))|≤
      bp (-(E.card:ℝ))*((num (I×J)+1)*bp (num I*num J*num J)*
        (bp (peakExpense I J t)*(ε^Fintype.card I*bp ((N:ℝ)*blockCompletionCost J*t))+
          bp ((peakExpense I J 1-(N:ℝ)/2)*t)))*fourierNorm w := by
  classical
  let F (M : Avenue I J) := if withinRail M E then
    vectorPhase (railsM E M) Z*avg unif (fun x=>phasedBy M x*(∏ i,f i (led i x))*
      w ((rackCoordinates (I×J) N).symm x)) else 0
  let L := ε^Fintype.card I*bp ((N:ℝ)*blockCompletionCost J*t)
  have hmask (M : Avenue I J) (hm : withinRail M E) : ∀ x y,¬P x.2 y.2→M x y=0 := by
    intro x y hxy
    exact hm x y (fun h=>hxy (hE (x,y) h))
  have hs M (ht : peak M<t) : |F M|≤L*fourierNorm w := by
    by_cases hm : withinRail M E
    · dsimp only [F]
      rw [if_pos hm,abs_mul,vectorPhase,wsign_abs,one_mul]
      refine (low_rank_batch_weight P M (hmask M hm) f ε hε hf w).trans ?_
      have hh : (peak M:ℝ)≤t := by exact_mod_cast ht.le
      apply mul_le_mul_of_nonneg_right _ (fourier_norm_nonneg w)
      exact mul_le_mul_of_nonneg_left (bp_le (mul_le_mul_of_nonneg_left hh
        (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg (blockCompletionCost J))))) (pow_nonneg hε _)
    · simp only [F,hm,if_false,abs_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg hε _) (bp_pos _).le) (fourier_norm_nonneg w)
  have hl M (_ht : t≤peak M) : |F M|≤bp (-((N:ℝ)/2)*peak M)*fourierNorm w := by
    by_cases hm : withinRail M E
    · dsimp only [F]
      rw [if_pos hm,abs_mul,vectorPhase,wsign_abs,one_mul]
      convert high_rank_batch_weight M f hb w using 1
      congr 2
      ring
    · simp only [F,hm,if_false,abs_zero]
      exact mul_nonneg (bp_pos _).le (fourier_norm_nonneg w)
  have hh := weighted_pattern_sum_bound F t L ((N:ℝ)/2) (fourierNorm w)
    (mul_nonneg (pow_nonneg hε _) (bp_pos _).le) (fourier_norm_nonneg w) hroom hs hl
  have he : avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*ind (traced x E Z))=
      bp (-(E.card:ℝ))*∑ M: Avenue I J,F M := by
    simp_rw [rail_expand,←avg_mul']
    rw [avg_avg]
    have hv v : avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)*
        (phasedBy (ledgerM E v) x*vectorPhase v Z))=
        vectorPhase v Z*avg unif (fun x=>phasedBy (ledgerM E v) x*(∏ i,f i (led i x))*
          w ((rackCoordinates (I×J) N).symm x)) := by
      rw [←avg_mul']
      apply avg_congr
      intro x _
      ring
    simp_rw [hv]
    have hu (v : Wgt (Vec E)) : avg unif v=bp (-(E.card:ℝ))*∑ x,v x := by
      unfold avg
      simp only [unif_apply,card_space,dim_vec,Fintype.card_coe,←bp_neg,←Finset.mul_sum]
    rw [hu]
    congr 1
    have hh := sum_ledger E (fun M=>vectorPhase (railsM E M) Z*avg unif
      (fun x=>phasedBy M x*(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)))
    simp only [inLedger] at hh
    exact hh
  rw [he,abs_mul,abs_of_pos (bp_pos _)]
  exact (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq (mul_assoc _ _ _).symm

end
end Lax793645Proofs.Simplifications
