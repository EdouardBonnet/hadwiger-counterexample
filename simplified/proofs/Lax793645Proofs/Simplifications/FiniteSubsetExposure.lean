import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SpanDeficits

namespace Lax793645Proofs.Simplifications
open Finset
open scoped BigOperators
noncomputable section
variable {I : Type} [DecidableEq I]

private def harmonicSum (n : ℕ) : ℝ := ∑ i ∈ range n, 1/((i:ℝ)+1)

private theorem harmonic_step (n : ℕ) :
    harmonicSum (n+1) = harmonicSum n + 1/((n:ℝ)+1) := by
  simp [harmonicSum,sum_range_succ]

private theorem harmonic_mono : Monotone harmonicSum :=
  monotone_nat_of_le_succ fun n => by rw [harmonic_step]; exact le_add_of_nonneg_right (by positivity)

private theorem harmonic_double (b : ℕ) (hb : 0 < b) :
    1/2 ≤ harmonicSum (2*b) - harmonicSum b := by
  rw [two_mul,harmonicSum,Finset.sum_range_add]
  have hpos : (0:ℝ) < b := by exact_mod_cast hb
  have h := Finset.sum_le_sum (s:=range b) (f:=fun _ => 1/(2*(b:ℝ)))
    (g:=fun i => 1/(((b+i:ℕ):ℝ)+1)) (fun i hi => by
      have hi' := Finset.mem_range.mp hi
      exact one_div_le_one_div_of_le (by positivity) (by push_cast; exact_mod_cast (show b+i+1 ≤ 2*b by omega)))
  have he : (∑ _i ∈ range b, 1/(2*(b:ℝ))) = 1/2 := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    field_simp
  rw [he] at h
  simpa only [harmonicSum,add_sub_cancel_left] using h

private theorem harmonic_blocks (m b : ℕ) (hb : 0 < b) :
    (m:ℝ)/2 ≤ harmonicSum (2^m*b) - harmonicSum b := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := harmonic_double (2^m*b) (by positivity)
    rw [pow_succ',Nat.mul_assoc]
    push_cast
    linarith only [h,ih]

/-- If a monotone set function has bounded total cost, one can leave a large
set whose individual increments are close to their combined increment.
The proof only compares a minimizing set with its one-element deletions. -/
theorem subset_with_small_marginals (W : Finset I) (D : Finset I → ℕ) (hD : Monotone D)
    (b m r : ℕ) (hb : 0 < b) (hW : W.card = 2^m*b) (hm : 16*r < m)
    (hbound : D W ≤ 2*r*W.card) :
    ∃ E R : Finset I, W = E ∪ R ∧ Disjoint E R ∧ b ≤ R.card ∧ ∀ i ∈ R,
      4*(R.card*(D (insert i E)-D E)) ≤ 4*(D W-D E)+R.card := by
  classical
  let cost (R : Finset I) : ℝ :=
    ((D W:ℝ) - D (W \ R))/R.card - harmonicSum R.card/4
  let choices := W.powerset.filter Finset.Nonempty
  have hcard : 0 < W.card := by rw [hW]; positivity
  have hWmem : W ∈ choices := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,card_pos.mp hcard⟩
  obtain ⟨R,hR,hmin⟩ := Finset.exists_min_image choices cost ⟨W,hWmem⟩
  obtain ⟨hRW,hne⟩ := mem_filter.mp hR
  have hsub : R ⊆ W := mem_powerset.mp hRW
  let E := W \ R
  have hEW : E ⊆ W := sdiff_subset
  have hrem : 0 ≤ (D W:ℝ) - D E := sub_nonneg.mpr (by exact_mod_cast hD hEW)
  have hsize : b < R.card := by
    by_contra! hle
    have hlog := harmonic_blocks m b hb
    rw [←hW] at hlog
    have hRle := harmonic_mono hle
    have hbest := hmin W hWmem
    change ((D W:ℝ)-D E)/R.card - harmonicSum R.card/4 ≤ _ at hbest
    have hinit : cost W ≤ 2*(r:ℝ) - harmonicSum W.card/4 := by
      apply sub_le_sub_right
      apply (div_le_iff₀ (by exact_mod_cast hcard : (0:ℝ)<W.card)).mpr
      have hD' : (D W:ℝ) ≤ 2*r*W.card := by exact_mod_cast hbound
      linarith only [hD',Nat.cast_nonneg (D (W \ W)) (α:=ℝ)]
    have hn := div_nonneg hrem (Nat.cast_nonneg R.card (α:=ℝ))
    linarith only [hlog,hRle,hbest.trans hinit,hn,show 16*(r:ℝ) < m by exact_mod_cast hm]
  refine ⟨E,R,(sdiff_union_of_subset hsub).symm,(Finset.disjoint_left.mpr fun _ hi => (mem_sdiff.mp hi).2), hsize.le,?_⟩
  intro i hi
  let R' := R.erase i
  have hcount : R'.card+1=R.card := card_erase_add_one hi
  have hpos : 0 < R'.card := by omega
  have hin : R' ∈ choices := mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset ..).trans hsub),card_pos.mp hpos⟩
  have hset : W \ R' = insert i E := by
    ext j
    by_cases h : j=i
    · subst j
      simp [R',hsub hi]
    simp [E,R',h]
  have hbest := hmin R' hin
  change ((D W:ℝ)-D E)/R.card - harmonicSum R.card/4 ≤
    ((D W:ℝ)-D (W \ R'))/R'.card - harmonicSum R'.card/4 at hbest
  rw [hset,←hcount,harmonic_step,Nat.cast_add,Nat.cast_one] at hbest
  have hpos' : (0:ℝ) < R'.card := by exact_mod_cast hpos
  have hpos'' : (0:ℝ) < R'.card+1 := by positivity
  field_simp at hbest
  rw [←hcount]
  have hinc : D E ≤ D (insert i E) := hD (subset_insert i E)
  have htot : D E ≤ D W := hD hEW
  apply Nat.cast_le (α:=ℝ) |>.mp
  push_cast [Nat.cast_sub hinc,Nat.cast_sub htot]
  nlinarith only [hbest]

end
end Lax793645Proofs.Simplifications
