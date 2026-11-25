import Lax793645Proofs.Simplifications.BlockRankCompletion

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def crossPart (M : Avenue I J) : Avenue I J := fun x y=>if x.1=y.1 then 0 else M x y

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem cross_part_inter (M : Avenue I J) : interDraw (crossPart M) := by
  intro i u v
  simp [crossPart]

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem cross_part_peak (M : Avenue I J) : peak (crossPart M)=peak M := by
  have he (t : ℕ) : arcPeak (crossPart M) t ↔ arcPeak M t := by
    constructor <;> rintro ⟨f,g,hd,hi⟩
    · refine ⟨f,g,hd,?_⟩
      have hh : (crossPart M).submatrix f g=M.submatrix f g := by
        ext i j; exact if_neg (hd i j)
      rwa [hh] at hi
    · refine ⟨f,g,hd,?_⟩
      have hh : (crossPart M).submatrix f g=M.submatrix f g := by
        ext i j; exact if_neg (hd i j)
      rwa [hh]
  unfold peak
  congr 1
  ext t
  exact he t

/-- Counting all coefficient patterns adds only the within-batch choices
to the existing disjoint-block rank count. -/
theorem count_full_patterns (t : ℕ) :
    nbr (fun M : Avenue I J=>peak M=t)≤bp (num I*num J*num J+peakExpense I J t) := by
  classical
  let S := {M : Avenue I J // peak M=t}
  let C := {M : Avenue I J // interDraw M ∧ peak M=t}
  let e : S→(I→Mat J J)×C := fun M=>(fun i u v=>M.val (i,u) (i,v),
    ⟨crossPart M.val,cross_part_inter _,(cross_part_peak _).trans M.property⟩)
  have hi : Injective e := by
    intro M Q h
    apply Subtype.ext
    ext ⟨i,u⟩ ⟨j,v⟩
    by_cases hij : i=j
    · subst j
      exact congr_fun (congr_fun (congr_fun (congrArg Prod.fst h) i) u) v
    · have hh := congr_fun (congr_fun (congrArg (fun z=>z.2.val) h) (i,u)) (j,v)
      change crossPart M.val (i,u) (j,v)=crossPart Q.val (i,u) (j,v) at hh
      simpa only [crossPart,hij,if_false] using hh
  have hc : (Fintype.card S:ℝ)≤(Fintype.card (I→Mat J J):ℝ)*(Fintype.card C:ℝ) := by
    exact_mod_cast (Fintype.card_le_of_injective e hi).trans_eq (Fintype.card_prod ..)
  have hd : (Fintype.card (I→Mat J J):ℝ)=bp (num I*num J*num J) := by
    rw [Fintype.card_fun,Nat.cast_pow]
    change (num (Mat J J))^Fintype.card I=_
    rw [cast_mat,←bp_mul_nat]
    congr 1
    unfold num
    ring
  rw [nbr_eq_card]
  refine hc.trans ?_
  rw [hd,bp_add]
  apply mul_le_mul_of_nonneg_left _ (bp_pos _).le
  simpa only [C,←nbr_eq_card] using price_peak (I:=I) (J:=J) t

/-- Exact stratification by cross-batch rank. -/
theorem sum_by_peak (f : ℕ→ℝ) :
    (∑ M : Avenue I J,f (peak M))=
      ∑ r : Fin (Fintype.card (I×J)+1),f r.val*nbr (fun M : Avenue I J=>peak M=r.val) := by
  classical
  unfold nbr tot
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  let r : Fin (Fintype.card (I×J)+1) := ⟨peak M,Nat.lt_succ_of_le (peak_le M)⟩
  rw [Finset.sum_eq_single r]
  · simp only [r,ind_true,mul_one]
  · intro s _ hs
    rw [ind_zero (fun h=>hs (Fin.ext h.symm)),mul_zero]
  · simp

omit [DecidableEq I] [DecidableEq J] in
theorem peak_expense_linear (r : ℕ) : peakExpense I J r=peakExpense I J 1*r := by
  unfold peakExpense
  norm_num
  ring

omit [DecidableEq I] [DecidableEq J] in
theorem peak_expense_nonneg (r : ℕ) : 0≤peakExpense I J r := by
  unfold peakExpense num
  positivity

/-- Explicit low/high-rank sum. The polynomial number of rank strata is
retained, so no asymptotic constant is hidden in the estimate. -/
theorem full_pattern_sum_bound (f : Avenue I J→ℝ) (t : ℕ) (L α : ℝ)
    (hL : 0≤L) (hα : peakExpense I J 1≤α)
    (hsmall : ∀ M,peak M<t→|f M|≤L)
    (hlarge : ∀ M,t≤peak M→|f M|≤bp (-α*peak M)) :
    |∑ M: Avenue I J,f M|≤
      (num (I×J)+1)*bp (num I*num J*num J)*
        (bp (peakExpense I J t)*L+bp ((peakExpense I J 1-α)*t)) := by
  classical
  let g (r : ℕ) := if r<t then L else bp (-α*r)
  have hg r : 0≤g r := by unfold g; split_ifs; exact hL; exact (bp_pos _).le
  have he M : |f M|≤g (peak M) := by
    unfold g
    split_ifs with h
    · exact hsmall M h
    · exact hlarge M (Nat.le_of_not_gt h)
  let B := num I*num J*num J
  let C := bp (B+peakExpense I J t)*L+bp (B+(peakExpense I J 1-α)*t)
  have hc r : g r*nbr (fun M : Avenue I J=>peak M=r)≤C := by
    refine (mul_le_mul_of_nonneg_left (count_full_patterns (I:=I) (J:=J) r) (hg r)).trans ?_
    by_cases hr : r<t
    · dsimp only [g]
      rw [if_pos hr]
      have hrt : (r:ℝ)≤t := by exact_mod_cast hr.le
      have hp : peakExpense I J r≤peakExpense I J t := by
        rw [peak_expense_linear r,peak_expense_linear t]
        exact mul_le_mul_of_nonneg_left hrt (peak_expense_nonneg 1)
      have h : L*bp (B+peakExpense I J r)≤L*bp (B+peakExpense I J t) :=
        mul_le_mul_of_nonneg_left (bp_le (by linarith)) hL
      calc
        _≤bp (B+peakExpense I J t)*L := h.trans_eq (mul_comm _ _)
        _≤C := le_add_of_nonneg_right (bp_pos _).le
    · dsimp only [g]
      rw [if_neg hr,←bp_add]
      have htr : (t:ℝ)≤r := by exact_mod_cast Nat.le_of_not_gt hr
      have hn : peakExpense I J 1-α≤0 := sub_nonpos.mpr hα
      have hpow : -α*r+(B+peakExpense I J r)≤B+(peakExpense I J 1-α)*t := by
        rw [peak_expense_linear r]
        nlinarith [mul_le_mul_of_nonpos_left htr hn]
      exact (bp_le hpow).trans (le_add_of_nonneg_left (mul_nonneg (bp_pos _).le hL))
  calc
    _≤∑ M: Avenue I J,|f M| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ M: Avenue I J,g (peak M) := Finset.sum_le_sum (fun M _=>he M)
    _=∑ r:Fin (Fintype.card (I×J)+1),g r.val*nbr (fun M: Avenue I J=>peak M=r.val) := sum_by_peak g
    _≤∑ _:Fin (Fintype.card (I×J)+1),C := Finset.sum_le_sum (fun r _=>hc r.val)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one,C,B,bp_add]
      unfold num
      ring

end
end Lax793645Proofs.Simplifications
