import Lax793645Proofs.Simplifications.UniformRawBatchBound

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] {N : ℕ}

theorem raw_budget_mono (ε η m a : ℝ) (hε : 0≤ε) (h : ε≤η) (d t : ℕ) :
    rawBatchBudget I J G N ε m a d t≤rawBatchBudget I J G N η m a d t := by
  unfold rawBatchBudget gramRankSum
  gcongr <;> simp only [bp,num] <;> positivity

/-- The three exponential contributions are kept separate: small cross
rank, large cross rank, and additional image kernels. -/
theorem raw_budget_exponents (m a v : ℝ) (d t : ℕ) :
    rawBatchBudget I J G N (bp (-v)) m a d t=
      ((8:ℝ)^Fintype.card G*(4:ℝ)^Fintype.card G*(num (I×J)+1))*
        (bp (num G*(2*m+4)*d+(N:ℝ)*(num G*2*a)+num I*num J*num J+
          peakExpense I J t+(N:ℝ)*blockCompletionCost J*t-v*num I)+
         bp (num G*(2*m+4)*d+(N:ℝ)*(num G*2*a)+num I*num J*num J+
          (peakExpense I J 1-(N:ℝ)/2)*t))+
      ((8:ℝ)^Fintype.card G*num G*16*(d+2))*
        bp (num G*(2*m+4)*d+(2*m+4)*d+((d:ℝ)+1)*(4*m-(N:ℝ))) := by
  unfold rawBatchBudget gramRankSum
  have hpow : bp ((2*m+4)*d)^Fintype.card G=bp (num G*(2*m+4)*d) := by
    rw [←bp_mul_nat]
    congr 1
    unfold num
    ring
  have hev : bp (-v)^Fintype.card I=bp (-(v*num I)) := by
    rw [←bp_mul_nat]
    congr 1
    unfold num
    ring
  rw [hpow,hev]
  simp only [sub_eq_add_neg,bp_add]
  ring

/-- Convenient form for choosing the Fourier threshold after all three
rank cutoffs have been fixed. -/
theorem raw_budget_exponent_bound (ε m a v : ℝ) (hε : 0≤ε) (hv : ε≤bp (-v))
    (d t : ℕ) :
    rawBatchBudget I J G N ε m a d t≤
      ((8:ℝ)^Fintype.card G*(4:ℝ)^Fintype.card G*(num (I×J)+1))*
        (bp (num G*(2*m+4)*d+(N:ℝ)*(num G*2*a)+num I*num J*num J+
          peakExpense I J t+(N:ℝ)*blockCompletionCost J*t-v*num I)+
         bp (num G*(2*m+4)*d+(N:ℝ)*(num G*2*a)+num I*num J*num J+
          (peakExpense I J 1-(N:ℝ)/2)*t))+
      ((8:ℝ)^Fintype.card G*num G*16*(d+2))*
        bp (num G*(2*m+4)*d+(2*m+4)*d+((d:ℝ)+1)*(4*m-(N:ℝ))) :=
  (raw_budget_mono ε (bp (-v)) m a hε hv d t).trans_eq (raw_budget_exponents m a v d t)

end
end Lax793645Proofs.Simplifications
