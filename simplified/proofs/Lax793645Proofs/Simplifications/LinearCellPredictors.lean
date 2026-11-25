import Lax793645Proofs.Simplifications.AffineQuadraticTests
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProductLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C T Y I J : Type} [Fintype C] [Fintype T] [Fintype Y]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def cellSlope (φ : F→C→F) (c : C) := φ 1 c+φ 0 c

omit [Fintype C] in
theorem cell_affine (φ : F→C→F) (q : F) (c : C) :
    φ q c=φ 0 c+cellSlope φ c*q := by
  rcases bit_cases q with h|h <;> subst q
  · simp
  · simp only [cellSlope,mul_one]
    have hh:=char_two (φ 0 c)
    linear_combination -hh

/-- Error is charged in the unnormalized product law. No inverse cell
mass appears, so arbitrarily small linear cells cause no loss. -/
theorem cell_slope_error (μ : Wgt C) (hμ : IsLaw μ) (φ : F→C→F)
    (q : C→Vec I→F) (Q : C→Mat I I)
    (hq : ∀ c,q c∈Stocks I 2) (hQ : ∀ c,polarize (q c) (Q c))
    (M : C→Mat J J) (P : C→Mat J I) (k : C→Vec J)
    (hr : ∀ c,2*(M c).rank<(Q c).rank) :
    pr μ (fun c=>cellSlope φ c=0)≤4*pr (pairW μ unif)
      (fun x=>φ (q x.1 x.2) x.1≠q x.1 x.2+
        evmat (M x.1) (P x.1 *ᵥ x.2+k x.1) (P x.1 *ᵥ x.2+k x.1)) := by
  classical
  have hc (c : C) : (1/4:ℝ)*ind (cellSlope φ c=0)≤pr unif
      (fun x=>φ (q c x) c≠q c x+evmat (M c) (P c *ᵥ x+k c) (P c *ᵥ x+k c)) := by
    by_cases hs : cellSlope φ c=0
    · rw [ind_one hs,mul_one]
      have he (x : Vec I) : φ (q c x) c=φ 0 c := by
        rw [cell_affine φ (q c x) c,hs,zero_mul,add_zero]
      simp_rw [he]
      have hh:=tester_affine_disagreement (q c) (Q c) (hq c) (hQ c)
        (M c) (P c) (k c) (φ 0 c) (hr c)
      convert hh using 2
      funext x
      apply propext
      generalize q c x+evmat (M c) (P c *ᵥ x+k c) (P c *ᵥ x+k c)=a
      rcases bit_cases a with h|h <;> rcases bit_cases (φ 0 c) with hb|hb <;>
        rw [h,hb] <;> decide
    · rw [ind_zero hs,mul_zero]
      exact pr_nonneg unif_law.nz
  have hh:=avg_mono hμ.nz hc
  simp only [pr,avg_mul'] at hh
  simp only [pr,pairW_avg]
  linarith only [hh]

/-- The common cell may encode correlated coordinates for all tags.
Only its independence from the shared tester is used. -/
theorem odd_cell_parity (μ : Wgt C) (hμ : IsLaw μ) (ν : Wgt Y) (hν : IsLaw ν)
    (q : Y→F) (a : ℝ) (ha : 0≤a) (hq : ∀ b : F,a≤pr ν (fun y=>q y=b))
    (φ : T→F→C→F) (hodd : Odd (Fintype.card T)) :
    a*(1-∑ t,pr μ (fun c=>cellSlope (φ t) c=0))≤
      pr (pairW μ ν) (fun x=>(∑ t,φ t (q x.2) x.1)≠0) := by
  classical
  let good (c : C) := ∀ t,cellSlope (φ t) c≠0
  have hc (c : C) : a*ind (good c)≤pr ν (fun y=>(∑ t,φ t (q y) c)≠0) := by
    by_cases hg : good c
    · rw [ind_one hg,mul_one]
      have hs (t : T) : cellSlope (φ t) c=1 := by
        rcases bit_cases (cellSlope (φ t) c) with h|h
        · exact (hg t h).elim
        exact h
      have he (b : F) : (∑ t,φ t b c)=(∑ t,φ t 0 c)+b := by
        simp_rw [cell_affine (φ _) b c,hs,one_mul]
        rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,odd_smul_bit hodd]
      rcases bit_cases (∑ t,φ t 0 c) with h|h
      · refine (hq 1).trans (pr_mono hν.nz fun y hy=>?_)
        rw [he,h,hy]
        decide
      · refine (hq 0).trans (pr_mono hν.nz fun y hy=>?_)
        rw [he,h,hy]
        decide
    · rw [ind_zero hg,mul_zero]
      exact pr_nonneg hν.nz
  have hh:=avg_mono hμ.nz hc
  have hh' : a*pr μ good≤pr (pairW μ ν) (fun x=>(∑ t,φ t (q x.2) x.1)≠0) := by
    simpa only [pr,avg_mul',pairW_avg] using hh
  have hb : 1-(∑ t,pr μ (fun c=>cellSlope (φ t) c=0))≤pr μ good := by
    have hu:=pr_exists_le hμ.nz (fun t c=>cellSlope (φ t) c=0)
    have he : (fun c=>∃ t,cellSlope (φ t) c=0)=(fun c=>¬good c) := by
      funext c
      simp [good]
    rw [he,pr_not,hμ.total] at hu
    linarith only [hu]
  exact (mul_le_mul_of_nonneg_left hb ha).trans hh'

/-- The two local errors force a fixed positive error. This is the
finite counting core of the proposed shorter predictor contradiction. -/
theorem linear_cell_predictor_gap (μ : Wgt C) (hμ : IsLaw μ)
    (ν : Wgt Y) (hν : IsLaw ν) (q : Y→F)
    (hq : ∀ b : F,(1/4:ℝ)≤pr ν (fun y=>q y=b))
    (φ : T→F→C→F) (hodd : Odd (Fintype.card T)) (ε : ℝ)
    (hs : ∀ t,pr μ (fun c=>cellSlope (φ t) c=0)≤4*ε)
    (hp : pr (pairW μ ν) (fun x=>(∑ t,φ t (q x.2) x.1)≠0)≤
      (Fintype.card T:ℝ)*ε) :
    1≤8*(Fintype.card T:ℝ)*ε := by
  have hh:=(odd_cell_parity μ hμ ν hν q (1/4) (by norm_num) hq φ hodd).trans hp
  have hb:=(Finset.sum_le_sum fun t (_ : t∈Finset.univ)=>hs t)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hb
  nlinarith only [hh,hb]

/-- Combining the rank test on each affine cell with the odd shared
identity gives the fixed lower error bound required by consistency. -/
theorem quadratic_cell_predictor_gap (μ : Wgt C) (hμ : IsLaw μ)
    (ν : Wgt Y) (hν : IsLaw ν) (q : Y→F)
    (hq : ∀ b : F,(1/4:ℝ)≤pr ν (fun y=>q y=b))
    (φ : T→F→C→F) (hodd : Odd (Fintype.card T)) (ε : ℝ)
    (Qtest : T→C→Vec I→F) (Q : T→C→Mat I I)
    (hpoly : ∀ t c,Qtest t c∈Stocks I 2)
    (hpolar : ∀ t c,polarize (Qtest t c) (Q t c))
    (M : T→C→Mat J J) (P : T→C→Mat J I) (k : T→C→Vec J)
    (hr : ∀ t c,2*(M t c).rank<(Q t c).rank)
    (he : ∀ t,pr (pairW μ unif)
      (fun x=>φ t (Qtest t x.1 x.2) x.1≠Qtest t x.1 x.2+
        evmat (M t x.1) (P t x.1 *ᵥ x.2+k t x.1) (P t x.1 *ᵥ x.2+k t x.1))≤ε)
    (hp : pr (pairW μ ν) (fun x=>(∑ t,φ t (q x.2) x.1)≠0)≤
      (Fintype.card T:ℝ)*ε) :
    1≤8*(Fintype.card T:ℝ)*ε := by
  apply linear_cell_predictor_gap μ hμ ν hν q hq φ hodd ε _ hp
  intro t
  exact (cell_slope_error μ hμ (φ t) (Qtest t) (Q t) (hpoly t) (hpolar t)
    (M t) (P t) (k t) (hr t)).trans (mul_le_mul_of_nonneg_left (he t) (by norm_num))

end
end Lax793645Proofs.Simplifications
