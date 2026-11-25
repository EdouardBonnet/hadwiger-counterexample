import Lax793645Proofs.Simplifications.MomentScaleAlgebra
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.HistogramEnergyScales

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter
noncomputable section
set_option maxHeartbeats 1000000

/-- The repetition fraction is fixed before the desired decay rate. -/
theorem raw_budget_calendar (J G : Type) [Fintype J] [Fintype G]
    (M : ℕ) (hM : 1 ≤ M) (i k : ℝ) (hi : 0 ≤ i) (hk : 0 ≤ k) :
    ∃  s : ℕ,0<s ∧ ∀ H : ℝ,0 ≤ H → ∃  a d t : ℕ,∃  v : ℝ,0 ≤ v ∧
      ∀ᶠ n : ℕ in atTop,
        0<n/s ∧ 2*(k*(n/s:ℕ))-(M*n:ℕ) ≤ (-1:ℝ) ∧
        peakExpense (Fin (n/s)) J 1 ≤ (M*n:ℕ)/2 ∧
        rawBatchBudget (Fin (n/s)) J G (M*n) (bp (-v)) (k*(n/s:ℕ)) a d t+
          bp ((3*(n/s:ℕ)*i-n)*a) ≤ bp (-H*n) := by
  let g:=num G
  let j:=num J
  let c:=2*(1+2*j)*j
  let b:ℝ:=blockCompletionCost J
  have hg : 0 ≤ g:=Nat.cast_nonneg _
  have hj : 0 ≤ j:=Nat.cast_nonneg _
  have hc : 0 ≤ c:=by positivity
  have hb : 0 ≤ b:=Nat.cast_nonneg _
  have hgk : 0 ≤ g*k:=mul_nonneg hg hk
  have hMr : (1:ℝ) ≤ M:=by exact_mod_cast hM
  obtain ⟨s,hs⟩:=exists_nat_gt (1+6*i+4*c+2*(2*g+10)*k+4*k)
  have hs0 : 0<s := by exact_mod_cast (show (0:ℝ)<s by nlinarith only [hs,hi,hc,hk,hgk])
  have hs1 : (1:ℝ) ≤ s:=by exact_mod_cast hs0
  have hsI : 6*i ≤ s:=by nlinarith only [hs,hi,hc,hk,hgk]
  have hsC : 4*c ≤ s:=by nlinarith only [hs,hi,hc,hk,hgk]
  have hsK : 2*(2*g+10)*k ≤ s:=by nlinarith only [hs,hi,hc,hk,hgk]
  have hsF : 4*k ≤ s:=by nlinarith only [hs,hi,hc,hk,hgk]
  refine ⟨s,hs0,fun H hH=>?_⟩
  let r:=H+1
  have hr : 0 ≤ r:=by dsimp [r]; linarith
  obtain ⟨a,ha⟩:=exists_nat_ge (2*r)
  obtain ⟨d,hd⟩:=exists_nat_ge (2*r)
  obtain ⟨t,ht⟩:=exists_nat_ge (4*(r+2*(M:ℝ)*g*a+2*g*k*d+j*j))
  let v:=2*(s:ℝ)*(r+2*(M:ℝ)*g*a+(M:ℝ)*b*t+2*g*k*d+j*j+c*t)
  have hv : 0 ≤ v:=by dsimp [v]; positivity
  let A:ℝ:=(8:ℝ)^Fintype.card G*(4:ℝ)^Fintype.card G
  let B:ℝ:=(8:ℝ)^Fintype.card G*g*16*(d+2)
  let C:=2*A*(j+1)*bp (4*g*d)+B*bp (4*(g+1)*d)+1
  have hA : 0 ≤ A:=by dsimp [A]; positivity
  have hB : 0 ≤ B:=by dsimp [B]; positivity
  have hC : 0 ≤ C:=by dsimp [C]; simp only [bp]; positivity
  refine ⟨a,d,t,v,hv,?_⟩
  filter_upwards [(div_grows s hs0).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 2,bp_poly_dom_nat (a:=1) (by norm_num) C 1] with n hl hn hpay
  let l:=n/s
  have hlr : 1 ≤ (l:ℝ):=by exact_mod_cast hl
  have hl0 : 0 ≤ (l:ℝ):=Nat.cast_nonneg _
  have hn1 : (1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
  have hn2 : (2:ℝ) ≤ n:=by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n:=Nat.cast_nonneg _
  have hsl : (s:ℝ)*l ≤ n:=by
    rw [mul_comm]
    exact_mod_cast Nat.div_mul_le_self n s
  have hnl : (n:ℝ) ≤ 2*s*l:=by
    have hh:=Nat.lt_mul_div_succ n hs0
    have hh' : (n:ℝ) ≤ s*((l:ℝ)+1):=by exact_mod_cast hh.le
    nlinarith only [hh',mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg s : (0:ℝ) ≤ s)]
  have hln : (l:ℝ) ≤ n:=by nlinarith only [hsl,mul_le_mul_of_nonneg_right hs1 hl0]
  have hmn : (n:ℝ) ≤ (M:ℝ)*n:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMr hn0
  have hci : c*l ≤ (M:ℝ)*n/4:=by
    nlinarith only [hsl,hmn,mul_le_mul_of_nonneg_right hsC hl0]
  have hki : (2*g+10)*k*l ≤ (n:ℝ)/2:=by
    nlinarith only [hsl,mul_le_mul_of_nonneg_right hsK hl0]
  have hii : 3*i*l ≤ (n:ℝ)/2:=by
    nlinarith only [hsl,mul_le_mul_of_nonneg_right hsI hl0]
  have hframe : 2*(k*l)-(M:ℝ)*n ≤ -1:=by
    nlinarith only [hsl,hmn,hn2,mul_le_mul_of_nonneg_right hsF hl0]
  have hpeak : peakExpense (Fin l) J 1=c*l:=by
    simp only [peakExpense,num,Fintype.card_fin,c,j]
    norm_num
    ring
  refine ⟨hl,by simpa only [Nat.cast_mul] using hframe,?_,?_⟩
  · rw [hpeak,Nat.cast_mul]
    nlinarith only [hci,hmn,hn0]
  have hnom:=nominal_exponent_bound i l n a r hn0 (Nat.cast_nonneg a) hii ha
  have hker:=image_kernel_exponent_bound g k l n ((M:ℝ)*n) d r hg hk hl0 hn0
    (Nat.cast_nonneg d) hmn hki hd
  have hhigh:=high_rank_exponent_bound g k j c l n M a d t r hg hk hn0
    (Nat.cast_nonneg d) (Nat.cast_nonneg t) hMr hln hci ht
  have hlow:=low_rank_exponent_bound g k j c b l n M a d t r s v hg hk hc hb
    (Nat.cast_nonneg M) (Nat.cast_nonneg a) (Nat.cast_nonneg d) (Nat.cast_nonneg t) hr hln hnl rfl
  have he : peakExpense (Fin l) J t=c*l*t:=by
    rw [peak_expense_linear,hpeak]
  rw [raw_budget_exponents,he,hpeak]
  simp only [num,Fintype.card_fin,Fintype.card_prod,Nat.cast_mul]
  change A*((l:ℝ)*j+1)*(bp (g*(2*(k*l)+4)*d+((M:ℝ)*n)*(g*2*a)+l*j*j+
      c*l*t+((M:ℝ)*n)*b*t-v*l)+
    bp (g*(2*(k*l)+4)*d+((M:ℝ)*n)*(g*2*a)+l*j*j+(c*l-(M:ℝ)*n/2)*t))+
    B*bp (g*(2*(k*l)+4)*d+(2*(k*l)+4)*d+((d:ℝ)+1)*(4*(k*l)-(M:ℝ)*n))+
    bp ((3*(l:ℝ)*i-n)*a) ≤ _
  have hmain : A*((l:ℝ)*j+1) ≤ A*(j+1)*n:=by
    have hh : (l:ℝ)*j+1 ≤ (j+1)*n:=by nlinarith only [hn1,mul_le_mul_of_nonneg_right hln hj]
    exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)
  have hmain0 : 0 ≤ A*((l:ℝ)*j+1):=by positivity
  have hnom'' : bp ((3*(l:ℝ)*i-n)*a) ≤ (n:ℝ)*bp (-r*n):=by
    exact (bp_le hnom).trans (by nlinarith only [hn1,bp_pos (-r*n)])
  have htail : B*bp (g*(2*(k*l)+4)*d+(2*(k*l)+4)*d+((d:ℝ)+1)*(4*(k*l)-(M:ℝ)*n)) ≤
      B*bp (4*(g+1)*d)*n*bp (-r*n):=by
    refine (mul_le_mul_of_nonneg_left (bp_le hker) hB).trans ?_
    rw [bp_add]
    have hh : 0 ≤ B*bp (4*(g+1)*d)*bp (-r*n):=by simp only [bp]; positivity
    nlinarith only [mul_le_mul_of_nonneg_left hn1 hh]
  have hfirst : A*((l:ℝ)*j+1)*
      (bp (g*(2*(k*l)+4)*d+((M:ℝ)*n)*(g*2*a)+l*j*j+c*l*t+((M:ℝ)*n)*b*t-v*l)+
       bp (g*(2*(k*l)+4)*d+((M:ℝ)*n)*(g*2*a)+l*j*j+(c*l-(M:ℝ)*n/2)*t)) ≤
      2*A*(j+1)*bp (4*g*d)*n*bp (-r*n):=by
    refine (mul_le_mul hmain (add_le_add (bp_le hlow) (bp_le hhigh))
      (by exact add_nonneg (bp_pos _).le (bp_pos _).le) (by positivity)).trans_eq ?_
    rw [bp_add]
    ring
  have hsum:=(add_le_add (add_le_add hfirst htail) hnom'')
  have hfinal : C*(n:ℝ)*bp (-r*n) ≤ bp (-H*n):=by
    have hp : C*(n:ℝ) ≤ bp (n:ℝ):=by simpa only [pow_one,one_mul] using hpay.le
    refine (mul_le_mul_of_nonneg_right hp (bp_pos _).le).trans_eq ?_
    rw [←bp_add]
    congr 1
    dsimp only [r]
    ring
  exact hsum.trans ((show 2*A*(j+1)*bp (4*g*d)*n*bp (-r*n)+
    B*bp (4*(g+1)*d)*n*bp (-r*n)+n*bp (-r*n)=C*n*bp (-r*n) by dsimp only [C]; ring).le.trans hfinal)

end
end Lax793645Proofs.Simplifications
