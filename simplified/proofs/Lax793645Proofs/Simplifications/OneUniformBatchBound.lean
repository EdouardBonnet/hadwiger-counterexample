import Lax793645Proofs.Simplifications.OneRawBatchBound

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}

/-- A uniform numerical budget once nominal deficiencies are bounded. -/
def oneRawBatchBudget (I J G : Type) [Fintype I] [Fintype J] [Fintype G]
    (N : ℕ) (ε m a : ℝ) (d t : ℕ) : ℝ :=
  (8:ℝ)^Fintype.card G*bp ((2*m+4)*d)^Fintype.card G*
    ((4:ℝ)^Fintype.card G*bp ((N:ℝ)*(num G*2*a))*quadraticPatternBudget I J N ε t+
      num G*(16*(d+2)*bp ((2*m+4)*d+((d:ℝ)+1)*(4*m-(N:ℝ)))))

omit [DecidableEq I] [DecidableEq J] [DecidableEq G] in
theorem one_raw_batch_budget_nonneg (ε m a : ℝ) (hε : 0≤ε) (d t : ℕ) :
    0≤oneRawBatchBudget I J G N ε m a d t := by
  classical
  unfold oneRawBatchBudget
  apply mul_nonneg
  · exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (bp_pos _).le _)
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (bp_pos _).le)
      (quadratic_pattern_budget_nonneg ε hε t)
  · apply mul_nonneg (Nat.cast_nonneg _)
    exact mul_nonneg (by positivity) (bp_pos _).le

/-- No individual nominal rank remains in the bound; only a slot bound
and a uniform deficiency bound occur. -/
theorem one_raw_frame_uniform_bound (g : Route (I×J) G) (mixer : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) (A : NomQuery p n g)
    (m a : ℝ) (hm : 0≤m) (hslots : ∀ i,num (Port g i)≤m)
    (hdef : ∀ i,num (Port g i)-(A i).rank≤a) (hroom : 2*m+2 ≤ N)
    (P : J→J→Prop) [DecidableRel P] (hP : ∀ u v,P u v → P v u) (hmask : ∀ v∈crowded g,P v.1.2 v.2.2)
    (f : I→Wgt (Rack J N)) (ε : ℝ) (hε : 0≤ε) (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ (M : Mat J J),Mᵀ=M → (∀ u v,¬P u v→M u v=0)→∀ i ξ,
      |linearFourier (fun x=>phasedBy M (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤ε)
    (d t : ℕ) (hrank : peakExpense I J 1≤(N:ℝ)/2) :
    |avg (oneForumLaw mixer N) (fun x=>∏ i,f i (led i (onePeek g A x)))|≤
      oneRawBatchBudget I J G N ε m a d t := by
  let B:=bp ((2*m+4)*d)
  have hB : 1≤B := by
    dsimp only [B]
    rw [←bp_zero]
    apply bp_le
    exact mul_nonneg (by linarith) (Nat.cast_nonneg d)
  have hB0 : 0≤B := (by norm_num : (0:ℝ)≤1).trans hB
  have hr i : ((A i).rank:ℝ)≤m :=
    (show ((A i).rank:ℝ)≤num (Port g i) by exact_mod_cast (A i).rank_le_card_width).trans (hslots i)
  have hc i : singleKernelSieveCost (Fin (A i).rank) d≤B := by
    refine (single_kernel_sieve_exponential d).trans (bp_le ?_)
    simp only [num,Fintype.card_fin]
    nlinarith [hr i,mul_le_mul_of_nonneg_right (hr i) (Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hh:=one_raw_frame_bound g mixer hN A (fun i=>by linarith [hr i])
    P hP hmask f ε hε hb hf d t hrank B hB hc
  have hcost : (∏ i,singleKernelSieveCost (Fin (A i).rank) d)≤B^Fintype.card G := by
    exact (Finset.prod_le_prod (fun i _=>(single_sieve_cost_ge_one (R:=Fin (A i).rank) d).trans'
      (by norm_num)) (fun i _=>hc i)).trans_eq (by simp)
  have hnom : (∑ i,(num (Port g i)-(A i).rank))≤num G*a := by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hdef i)
    exact hh.trans_eq (by simp only [Finset.sum_const,card_univ,nsmul_eq_mul,num])
  have hexp := bp_le (mul_le_mul_of_nonneg_left hnom (show (0:ℝ)≤2*N by positivity))
  rw [show 2*(N:ℝ)*(num G*a)=(N:ℝ)*(num G*2*a) by ring] at hexp
  have htail : (∑ i,16*(d+2)*bp ((((A i).rank:ℝ)+2)*d+
      ((d:ℝ)+1)*(4*((A i).rank:ℝ)-(N:ℝ))))≤
      num G*(16*(d+2)*bp ((2*m+4)*d+((d:ℝ)+1)*(4*m-(N:ℝ)))) := by
    have h i : 16*(d+2)*bp ((((A i).rank:ℝ)+2)*d+
        ((d:ℝ)+1)*(4*((A i).rank:ℝ)-(N:ℝ)))≤
        16*(d+2)*bp ((2*m+4)*d+((d:ℝ)+1)*(4*m-(N:ℝ))) := by
      apply mul_le_mul_of_nonneg_left (bp_le _) (by positivity)
      nlinarith [hr i,mul_le_mul_of_nonneg_right (hr i) (Nat.cast_nonneg d : (0:ℝ)≤d)]
    exact (Finset.sum_le_sum (fun i _=>h i)).trans_eq (by simp only [Finset.sum_const,card_univ,nsmul_eq_mul,num])
  refine hh.trans ?_
  have hK:=quadratic_pattern_budget_nonneg (I:=I) (J:=J) (N:=N) ε hε t
  have h4 : 0≤(4:ℝ)^Fintype.card G:=pow_nonneg (by norm_num) _
  have h8 : 0≤(8:ℝ)^Fintype.card G:=pow_nonneg (by norm_num) _
  have hpB : 0≤B^Fintype.card G:=pow_nonneg hB0 _
  have hfirst := mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h4) hK)
    hcost (Finset.prod_nonneg (fun i _=>(single_sieve_cost_ge_one (R:=Fin (A i).rank) d).trans' (by norm_num)))
    (mul_nonneg (mul_nonneg h4 (bp_pos _).le) hK)
  have hsecond:=mul_le_mul_of_nonneg_left htail hpB
  have htotal:=mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) h8
  refine htotal.trans_eq ?_
  unfold oneRawBatchBudget
  change _=(8:ℝ)^Fintype.card G*B^Fintype.card G*_
  ring

end
end Lax793645Proofs.Simplifications
