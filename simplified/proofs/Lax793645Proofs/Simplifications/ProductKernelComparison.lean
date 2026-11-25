import Lax793645Proofs.Simplifications.PrescribedKernelGram

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G A : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] [Fintype A]

omit [Fintype G] in
/-- Multiplying any finite collection of relation and sieve weights keeps
an explicit product bound on its Fourier norm. -/
theorem fourier_norm_finset_product (s : Finset G) (f : G→Wgt (Vec I)) :
    fourierNorm (fun x=>∏ i∈s,f i x)≤∏ i∈s,fourierNorm (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,fourier_norm_const,abs_one,le_refl]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (fourier_norm_mul _ _).trans (mul_le_mul_of_nonneg_left ih (fourier_norm_nonneg _))

theorem fourier_norm_product (f : G→Wgt (Vec I)) :
    fourierNorm (fun x=>∏ i,f i x)≤∏ i,fourierNorm (f i) :=
  fourier_norm_finset_product univ f

/-- All prescribed nominal relations can be kept simultaneously, even
when their linear equations involve every original query batch. -/
theorem fourier_norm_relation_family {J : G→Type} [∀ i,Fintype (J i)] [∀ i,DecidableEq (J i)]
    (T : ∀ i,Vec I→ₗ[F] Vec (J i)) :
    fourierNorm (fun x=>ind (∀ i,T i x=0))=1 := by
  apply le_antisymm
  · simp only [ind_all]
    exact (fourier_norm_product (fun i x=>ind (T i x=0))).trans_eq (by
      simp only [linear_relation_fourier_norm,Finset.prod_const_one])
  have hh:=fourier_norm_point (fun x=>ind (∀ i,T i x=0)) 0
  simpa only [map_zero,forall_true_iff,ind_true,abs_one] using hh

omit [Fintype G] in
/-- A product approximation with a bounded number of factors. The loose
power deliberately avoids exceptional empty/singleton cases. -/
theorem product_difference_bound (s : Finset G) (a b : G→ℝ) (B : ℝ) (hB : 1≤B)
    (ha : ∀ i∈s,|a i|≤B) (hb : ∀ i∈s,|b i|≤B) :
    |(∏ i∈s,a i)-(∏ i∈s,b i)|≤B^s.card*∑ i∈s,|a i-b i| := by
  have hB0 : 0≤B := le_trans (by norm_num) hB
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hiA := ha i (mem_insert_self i s)
    have hsA j hj := ha j (mem_insert_of_mem hj)
    have hsB j hj := hb j (mem_insert_of_mem hj)
    have hd := ih hsA hsB
    have hp : |∏ j∈s,b j|≤B^s.card := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) hsB).trans_eq (by simp)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.card_insert_of_notMem hi,
      Finset.sum_insert hi,pow_succ]
    have he : a i*(∏ j∈s,a j)-b i*(∏ j∈s,b j)=
      a i*((∏ j∈s,a j)-(∏ j∈s,b j))+(a i-b i)*(∏ j∈s,b j) := by ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    have h1:=mul_le_mul hiA hd (abs_nonneg _) hB0
    have h2:=mul_le_mul_of_nonneg_left hp (abs_nonneg (a i-b i))
    have h3:=mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 s.card)
    have h4:=mul_le_mul_of_nonneg_left h3 (abs_nonneg (a i-b i))
    nlinarith

/-- Simultaneous sieve error, valid for a joint test depending on all
components. Only the separate marginal L1 errors are required. -/
theorem product_average_error (μ : Wgt A) (hμ : ∀ x,0≤μ x)
    (a b : G→Wgt A) (f : Wgt A) (hf : ∀ x,|f x|≤1)
    (B : ℝ) (hB : 1≤B) (ha : ∀ i x,|a i x|≤B) (hb : ∀ i x,|b i x|≤B)
    (ε : G→ℝ) (herr : ∀ i,avg μ (fun x=>|a i x-b i x|)≤ε i) :
    |avg μ (fun x=>f x*((∏ i,a i x)-(∏ i,b i x)))|≤
      B^Fintype.card G*∑ i,ε i := by
  refine (abs_avg_le hμ).trans ?_
  have hp x : |f x*((∏ i,a i x)-(∏ i,b i x))|≤
      B^Fintype.card G*∑ i,|a i x-b i x| := by
    rw [abs_mul]
    have hh:=product_difference_bound univ (fun i=>a i x) (fun i=>b i x) B hB
      (fun i _=>ha i x) (fun i _=>hb i x)
    exact ((mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)).trans_eq (one_mul _)).trans
      (by simpa only [card_univ] using hh)
  refine (avg_mono hμ hp).trans ?_
  rw [avg_mul',avg_sum]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>herr i))
    (pow_nonneg (le_trans (by norm_num) hB) _)

/-- A bound against every signed bounded test also controls the L1 error. -/
theorem l1_from_signed_tests (μ : Wgt A) (v : Wgt A) (ε : ℝ)
    (h : ∀ f : Wgt A,(∀ x,|f x|≤1)→|avg μ (fun x=>f x*v x)|≤ε) :
    avg μ (fun x=>|v x|)≤ε := by
  let f x : ℝ:=if 0≤v x then 1 else -1
  have hf x : |f x|≤1 := by dsimp only [f]; split <;> norm_num
  have he x : f x*v x=|v x| := by
    dsimp only [f]
    split
    · rename_i hx
      rw [one_mul,abs_of_nonneg hx]
    · rename_i hx
      rw [neg_one_mul,abs_of_neg (lt_of_not_ge hx)]
  have hh:=h f hf
  simp only [he] at hh
  exact (le_abs_self _).trans hh

end
end Lax793645Proofs.Simplifications
