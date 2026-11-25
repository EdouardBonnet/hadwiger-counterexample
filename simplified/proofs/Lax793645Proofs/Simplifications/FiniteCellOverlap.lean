import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectedSurrogates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
open scoped BigOperators Classical
noncomputable section
variable {A I : Type} [Fintype A] [Fintype I]

theorem weighted_cell_sum (u : Wgt A) (P : A→I) (a : Wgt I) (E : A→Prop) :
    avg u (fun x=>a (P x)*ind (E x))=
      ∑ i,a i*pr u (fun x=>E x ∧ P x=i) := by
  have he x : a (P x)*ind (E x)=∑ i,a i*ind (E x ∧ P x=i) := by
    rw [Finset.sum_eq_single (P x)]
    · simp only [and_true]
    · intro j _ hj
      rw [ind_zero (fun h=>hj h.2.symm),mul_zero]
    · simp
  simp_rw [he,avg_sum,avg_mul']
  rfl

/-- A bounded function constant on cells transfers a lower bound for
cell masses. The additive cell error is paid only once per cell. -/
theorem weighted_cell_lower (u ν : Wgt A) (P : A→I) (a : Wgt I) (E : A→Prop)
    (κ δ B : ℝ) (hδ : 0≤δ) (ha : ∀ i,0≤a i ∧ a i≤B)
    (hcell : ∀ i,κ*pr ν (fun x=>E x ∧ P x=i)-δ≤pr u (fun x=>E x ∧ P x=i)) :
    κ*avg ν (fun x=>a (P x)*ind (E x))-B*Fintype.card I*δ≤
      avg u (fun x=>a (P x)*ind (E x)) := by
  rw [weighted_cell_sum,weighted_cell_sum]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    mul_le_mul_of_nonneg_left (hcell i) (ha i).1)
  have he : (∑ i,a i*δ)≤B*Fintype.card I*δ := by
    calc _≤∑ _i:I,B*δ:=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (ha i).2 hδ
         _=B*Fintype.card I*δ:=by simp; ring
  simp_rw [mul_sub] at hh
  rw [Finset.sum_sub_distrib] at hh
  have hsum : (∑ i,a i*(κ*pr ν (fun x=>E x ∧ P x=i)))=
      κ*∑ i,a i*pr ν (fun x=>E x ∧ P x=i) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hsum] at hh
  linarith only [hh,he]

private theorem clipping_pointwise (u v g B R : ℝ)
    (hu : 0≤u) (hv : 0≤v) (hg : 0≤g) (hB : g≤B) (hR : 0≤R) :
    u*g≤u*v+R*|v-g|+B*u*ind (R≤u) := by
  by_cases h : R≤u
  · rw [ind_one h,mul_one]
    have hh:=mul_le_mul_of_nonneg_left hB hu
    nlinarith only [hh,mul_nonneg hu hv,mul_nonneg hR (abs_nonneg (v-g))]
  rw [ind_zero h,mul_zero,add_zero]
  have h1 : g-v≤|v-g| := by simpa only [abs_sub_comm] using le_abs_self (g-v)
  have h2:=mul_le_mul_of_nonneg_left h1 hu
  have h3:=mul_le_mul_of_nonneg_right (le_of_not_ge h) (abs_nonneg (v-g))
  nlinarith only [h2,h3]

/-- The overlap comparison uses one clipping height and one L1 error.
No level set or finite family of unions of cells is required. -/
theorem clipped_overlap_comparison (ν x y g : Wgt A) (E : A→Prop)
    (hν : ∀ a,0≤ν a) (hx : ∀ a,0≤x a) (hy : ∀ a,0≤y a)
    (hs : lsupp x ν) (ht : lsupp y ν) (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hg : ∀ a,0≤g a ∧ g a≤B) :
    avg x (fun a=>g a*ind (E a))≤overlap ν x y+
      R*varOne y (fun a=>ν a*g a)+B*pr x (fun a=>R≤density ν x a) := by
  have hrec a : x a=ν a*density ν x a:=congrFun (dresso ν x hs) a
  have hyrec a : y a=ν a*density ν y a:=congrFun (dresso ν y ht) a
  simp only [overlap,varOne,pr,avg]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hu : 0≤density ν x a:=div_nonneg (hx a) (hν a)
  have hv : 0≤density ν y a:=div_nonneg (hy a) (hν a)
  have hh:=mul_le_mul_of_nonneg_left
    (clipping_pointwise (density ν x a) (density ν y a) (g a) B R hu hv
      (hg a).1 (hg a).2 hR) (hν a)
  have he : |y a-ν a*g a|=ν a*|density ν y a-g a| := by
    rw [hyrec a,←mul_sub,abs_mul,abs_of_nonneg (hν a)]
  have hi : x a*(g a*ind (E a))≤x a*g a := by
    nlinarith only [ind_le_one (E a),mul_nonneg (hx a) (hg a).1]
  rw [he,hrec a] at *
  nlinarith only [hh,hi]

/-- A lower bound for the overlap of the two actual query measures.
The cell error is paid on the first side. The second side needs only
one bounded approximation. All masses in the formula are unnormalized. -/
theorem actual_cell_overlap (ν x y : Wgt A) (P : A→I) (a : Wgt I) (E : A→Prop)
    (κ δ B R : ℝ) (hκ : 0≤κ) (hδ : 0≤δ) (hB : 0≤B) (hR : 0≤R)
    (hν : ∀ k,0≤ν k) (hx : ∀ k,0≤x k) (hy : ∀ k,0≤y k)
    (hs : lsupp x ν) (ht : lsupp y ν) (ha : ∀ i,0≤a i ∧ a i≤B)
    (hcell : ∀ i,κ*pr ν (fun k=>E k ∧ P k=i)-δ ≤ pr x (fun k=>E k ∧ P k=i)) :
    κ*pr y E ≤ overlap ν x y + B*Fintype.card I*δ +
      (κ+R)*varOne y (fun k=>ν k*a (P k)) + B*pr x (fun k=>R≤density ν x k) := by
  let z := fun k=>ν k*a (P k)
  have hm : pr z E=avg ν (fun k=>a (P k)*ind (E k)) := by
    unfold pr avg z
    exact sum_congr rfl (fun k _=>mul_assoc ..)
  have hv := var_pr y z E
  rw [hm] at hv
  have hc := weighted_cell_lower x ν P a E κ δ B hδ ha hcell
  have ho := clipped_overlap_comparison ν x y (fun k=>a (P k)) E hν hx hy hs ht B R hB hR (fun k=>ha (P k))
  nlinarith only [mul_le_mul_of_nonneg_left hv hκ,hc,ho]

end
end Lax793645Proofs.Simplifications
