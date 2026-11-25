import Lax793645Proofs.Simplifications.RawBudgetExponents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section

/-- All cutoff choices are numerical and are made before the dimension. -/
theorem nominal_exponent_bound (i l n a r : ℝ)
    (hn : 0≤n) (ha : 0≤a) (hi : 3*i*l≤n/2) (hr : 2*r≤a) :
    (3*l*i-n)*a≤-r*n := by
  nlinarith [mul_le_mul_of_nonneg_right hi ha,mul_le_mul_of_nonneg_right hr hn]

theorem image_kernel_exponent_bound (g k l n N d r : ℝ)
    (hg : 0≤g) (hk : 0≤k) (hl : 0≤l) (hn : 0≤n) (hd : 0≤d)
    (hN : n≤N) (hscale : (2*g+10)*k*l≤n/2) (hr : 2*r≤d) :
    g*(2*(k*l)+4)*d+(2*(k*l)+4)*d+(d+1)*(4*(k*l)-N)≤
      -r*n+4*(g+1)*d := by
  have hh:=mul_le_mul_of_nonneg_right hscale (show 0≤d+1 by linarith)
  have hN':=mul_le_mul_of_nonneg_left hN (show 0≤d+1 by linarith)
  have hr':=mul_le_mul_of_nonneg_right hr hn
  nlinarith [mul_nonneg (mul_nonneg hk hl) hd,mul_nonneg hg (mul_nonneg hk hl)]

theorem high_rank_exponent_bound (g k j c l n M a d t r : ℝ)
    (hg : 0≤g) (hk : 0≤k) (hn : 0≤n) (hd : 0≤d) (ht : 0≤t)
    (hM : 1≤M) (hl : l≤n) (hscale : c*l≤M*n/4)
    (hcut : 4*(r+2*M*g*a+2*g*k*d+j*j)≤t) :
    g*(2*(k*l)+4)*d+(M*n)*(g*2*a)+l*j*j+(c*l-M*n/2)*t≤
      -r*n+4*g*d := by
  have hj : 0≤j*j:=mul_self_nonneg j
  have hp : 0≤2*g*k*d+j*j := by positivity
  have hln:=mul_le_mul_of_nonneg_left hl hp
  have hc:=mul_le_mul_of_nonneg_right hscale ht
  have hnM:=mul_le_mul_of_nonneg_right hM hn
  have hnt:=mul_le_mul_of_nonneg_right hnM ht
  have hcut':=mul_le_mul_of_nonneg_right hcut hn
  nlinarith

theorem low_rank_exponent_bound (g k j c b l n M a d t r s v : ℝ)
    (hg : 0≤g) (hk : 0≤k) (hc : 0≤c) (hb : 0≤b)
    (hM : 0≤M) (ha : 0≤a) (hd : 0≤d) (ht : 0≤t) (hr : 0≤r)
    (hl : l≤n) (hscale : n≤2*s*l)
    (hv : v=2*s*(r+2*M*g*a+M*b*t+2*g*k*d+j*j+c*t)) :
    g*(2*(k*l)+4)*d+(M*n)*(g*2*a)+l*j*j+c*l*t+(M*n)*b*t-v*l≤
      -r*n+4*g*d := by
  have hj : 0≤j*j:=mul_self_nonneg j
  have hp : 0≤2*g*k*d+j*j+c*t := by positivity
  have hln:=mul_le_mul_of_nonneg_left hl hp
  have hq : 0≤r+2*M*g*a+M*b*t+2*g*k*d+j*j+c*t := by positivity
  have hs:=mul_le_mul_of_nonneg_left hscale hq
  rw [hv]
  nlinarith

end
end Lax793645Proofs.Simplifications
