import Lax793645Proofs.Simplifications.OneAuxiliaryQueryMoments
import Lax793645Proofs.Simplifications.MomentScaleAlgebra
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.HistogramEnergyScales

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter
noncomputable section
set_option maxHeartbeats 1000000

theorem auxiliary_budget_exponents (I J G : Type) [Fintype I] [Fintype J] [Fintype G]
    (N : ℕ) (δ v : ℝ) (hδ : 0 ≤ δ) (hv : δ+bp (-(N:ℝ)/2) ≤ bp (-v)) (a t : ℕ) :
    auxiliaryRawBudget I J G N δ a t ≤ 
      (4:ℝ)^Fintype.card G*(num (I×(Bool×J))+1)*
        (bp ((N:ℝ)*(num G*2*a)+num I*num (Bool×J)*num (Bool×J)+
          peakExpense I (Bool×J) t+(N:ℝ)*symmetricCompletionCost (Bool×J)*t-v*num I)+
         bp ((N:ℝ)*(num G*2*a)+num I*num (Bool×J)*num (Bool×J)+
          (peakExpense I (Bool×J) 1-(N:ℝ)/2)*t)) := by
  have hh : auxiliaryRawBudget I J G N δ a t ≤ 
      (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*num G*a)*
        quadraticPatternBudget I (Bool×J) N (bp (-v)) t:=by
    unfold auxiliaryRawBudget quadraticPatternBudget
    gcongr <;> simp only [bp,num] <;> positivity
  refine hh.trans_eq ?_
  unfold quadraticPatternBudget
  have he : bp (-v)^Fintype.card I=bp (-(v*num I)):=by
    rw [←bp_mul_nat]
    congr 1
    unfold num
    ring
  rw [he]
  simp only [sub_eq_add_neg,bp_add]
  ring

/-- Only nominal deficiency and cross-batch rank have cutoffs. The
repetition rate is fixed before the requested exponential decay. -/
theorem auxiliary_even_budget_calendar (J G : Type) [Fintype J] [Fintype G]
    (M : ℕ) (hM : 1 ≤ M) (i k : ℝ) (hi : 0 ≤ i) (hk : 0 ≤ k) :
    ∃ s : ℕ,0<s ∧ ∀ H : ℝ,0 ≤ H → ∃ a t : ℕ,∃ δ : ℝ,0<δ ∧
      ∀ᶠ n : ℕ in atTop,
        0<2*(n/(2*s)) ∧ 2*(k*(2*(n/(2*s)):ℕ))+2 ≤ (M*n:ℕ) ∧
        peakExpense (Fin (2*(n/(2*s)))) (Bool×J) 1 ≤ (M*n:ℕ)/2 ∧
        auxiliaryRawBudget (Fin (2*(n/(2*s)))) J G (M*n) δ a t+
          bp ((3*(2*(n/(2*s)):ℕ)*i-n)*a) ≤ bp (-H*n) := by
  let g:=num G
  let j:=num (Bool×J)
  let c:=2*(1+2*j)*j
  let b:ℝ:=symmetricCompletionCost (Bool×J)
  have hg : 0 ≤ g:=Nat.cast_nonneg _
  have hj : 0 ≤ j:=Nat.cast_nonneg _
  have hc : 0 ≤ c:=by positivity
  have hb : 0 ≤ b:=Nat.cast_nonneg _
  have hMr : (1:ℝ) ≤ M:=by exact_mod_cast hM
  obtain ⟨s,hs⟩:=exists_nat_gt (1+6*i+4*c+4*k)
  have hs0 : 0<s:=by exact_mod_cast (show (0:ℝ)<s by nlinarith only [hs,hi,hc,hk])
  have hs1 : (1:ℝ) ≤ s:=by exact_mod_cast hs0
  have hsI : 6*i ≤ s:=by nlinarith only [hs,hi,hc,hk]
  have hsC : 4*c ≤ s:=by nlinarith only [hs,hi,hc,hk]
  have hsF : 4*k ≤ s:=by nlinarith only [hs,hi,hc,hk]
  refine ⟨s,hs0,fun H hH=>?_⟩
  let r:=H+1
  have hr : 0 ≤ r:=by dsimp [r]; linarith
  obtain ⟨a,ha⟩:=exists_nat_ge (2*r)
  obtain ⟨t,ht⟩:=exists_nat_ge (4*(r+2*(M:ℝ)*g*a+j*j))
  let v:=2*(s:ℝ)*(r+2*(M:ℝ)*g*a+(M:ℝ)*b*t+j*j+c*t)
  let A:ℝ:=(4:ℝ)^Fintype.card G
  let C:=2*A*(j+1)+1
  have hA : 0 ≤ A:=by dsimp [A]; positivity
  refine ⟨a,t,bp (-(v+1)),bp_pos _,?_⟩
  obtain ⟨n₀,hn₀⟩:=exists_nat_ge (2*(v+1))
  filter_upwards [(div_grows (2*s) (by omega)).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 4,eventually_ge_atTop n₀,bp_poly_dom_nat (a:=1) (by norm_num) C 1]
    with n hl hn hn₀' hpay
  generalize hlval : 2*(n/(2*s))=l
  have hlr : 2 ≤ (l:ℝ):=by exact_mod_cast (show 2 ≤ l by omega)
  have hl0 : 0 ≤ (l:ℝ):=Nat.cast_nonneg _
  have hn1 : (1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
  have hn2 : (4:ℝ) ≤ n:=by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n:=Nat.cast_nonneg _
  have hsl : (s:ℝ)*l ≤ n:=by
    have hh:=Nat.div_mul_le_self n (2*s)
    have he : s*l=(n/(2*s))*(2*s):=by rw [←hlval]; ring
    exact_mod_cast (show s*l ≤ n by rw [he]; exact hh)
  have hnl : (n:ℝ) ≤ 2*s*l:=by
    have hh:=Nat.lt_mul_div_succ n (show 0<2*s by omega)
    have hh' : (n:ℝ) ≤ (s:ℝ)*l+2*s:=by
      exact_mod_cast (show n ≤ s*l+2*s from hh.le.trans_eq (by rw [←hlval]; ring))
    nlinarith only [hh',mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg s : (0:ℝ) ≤ s)]
  have hln : (l:ℝ) ≤ n:=by nlinarith only [hsl,mul_le_mul_of_nonneg_right hs1 hl0]
  have hmn : (n:ℝ) ≤ (M:ℝ)*n:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMr hn0
  have hci : c*l ≤ (M:ℝ)*n/4:=by
    nlinarith only [hsl,hmn,mul_le_mul_of_nonneg_right hsC hl0]
  have hii : 3*i*l ≤ (n:ℝ)/2:=by
    nlinarith only [hsl,mul_le_mul_of_nonneg_right hsI hl0]
  have hframe : 2*(k*l)+2 ≤ (M:ℝ)*n:=by
    nlinarith only [hsl,hmn,hn2,mul_le_mul_of_nonneg_right hsF hl0]
  have hpeak : peakExpense (Fin l) (Bool×J) 1=c*l:=by
    simp only [peakExpense,num,Fintype.card_fin,c,j]
    norm_num
    ring
  refine ⟨by exact_mod_cast (by linarith only [hlr] : (0:ℝ)<l),
    by simpa only [Nat.cast_mul] using hframe,?_,?_⟩
  · rw [hpeak,Nat.cast_mul]
    nlinarith only [hci,hmn,hn0]
  have hnom:=nominal_exponent_bound i l n a r hn0 (Nat.cast_nonneg a) hii ha
  have hhigh:=high_rank_exponent_bound g 0 j c l n M a 0 t r hg (by norm_num) hn0
    (by norm_num) (Nat.cast_nonneg t) hMr hln hci (by simpa using ht)
  have hlow:=low_rank_exponent_bound g 0 j c b l n M a 0 t r s v hg (by norm_num) hc hb
    (Nat.cast_nonneg M) (Nat.cast_nonneg a) (by norm_num) (Nat.cast_nonneg t) hr hln hnl (by simp [v])
  simp only [mul_zero,zero_add,add_zero] at hhigh hlow
  have hsmall : bp (-(v+1))+bp (-((M*n:ℕ):ℝ)/2) ≤ bp (-v):=by
    have hn₀r : (n₀:ℝ) ≤ n:=by exact_mod_cast hn₀'
    have he : bp (-(v+1))+bp (-(v+1))=bp (-v):=by
      rw [show -(v+1)= -v-1 by ring,bp_sub]
      norm_num [show bp 1=2 from by norm_num [bp]]
    apply (add_le_add le_rfl (bp_le ?_)).trans_eq he
    rw [Nat.cast_mul]
    linarith
  have hraw:=auxiliary_budget_exponents (Fin l) J G (M*n) (bp (-(v+1))) v (bp_pos _).le hsmall a t
  have he : peakExpense (Fin l) (Bool×J) t=c*l*t:=by rw [peak_expense_linear,hpeak]
  rw [he,hpeak] at hraw
  simp only [num,Fintype.card_fin,Fintype.card_prod,Nat.cast_mul] at hraw
  have hjcast : (Fintype.card Bool:ℝ)*Fintype.card J=j:=by
    simp only [j,num,Fintype.card_prod,Nat.cast_mul]
  rw [hjcast] at hraw
  change auxiliaryRawBudget (Fin l) J G (M*n) (bp (-(v+1))) a t ≤ 
    A*((l:ℝ)*j+1)*(bp (((M:ℝ)*n)*(g*2*a)+l*j*j+c*l*t+((M:ℝ)*n)*b*t-v*l)+
      bp (((M:ℝ)*n)*(g*2*a)+l*j*j+(c*l-(M:ℝ)*n/2)*t)) at hraw
  have hmain : A*((l:ℝ)*j+1) ≤ A*(j+1)*n:=by
    have hh : (l:ℝ)*j+1 ≤ (j+1)*n:=by nlinarith only [hn1,mul_le_mul_of_nonneg_right hln hj]
    exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)
  have hfirst : auxiliaryRawBudget (Fin l) J G (M*n) (bp (-(v+1))) a t ≤ 
      2*A*(j+1)*n*bp (-r*n):=by
    refine hraw.trans ((mul_le_mul hmain (add_le_add (bp_le hlow) (bp_le hhigh))
      (add_nonneg (bp_pos _).le (bp_pos _).le) (by positivity)).trans_eq ?_)
    ring
  have htail : bp ((3*(l:ℝ)*i-n)*a) ≤ (n:ℝ)*bp (-r*n):=
    (bp_le hnom).trans (by nlinarith only [hn1,bp_pos (-r*n)])
  have hfinal : C*(n:ℝ)*bp (-r*n) ≤ bp (-H*n):=by
    have hp : C*(n:ℝ) ≤ bp (n:ℝ):=by simpa only [pow_one,one_mul] using hpay.le
    refine (mul_le_mul_of_nonneg_right hp (bp_pos _).le).trans_eq ?_
    rw [←bp_add]
    congr 1
    dsimp only [r]
    ring
  exact (add_le_add hfirst htail).trans ((show
    2*A*(j+1)*n*bp (-r*n)+n*bp (-r*n)=C*n*bp (-r*n) by dsimp only [C]; ring).le.trans hfinal)

end
end Lax793645Proofs.Simplifications
