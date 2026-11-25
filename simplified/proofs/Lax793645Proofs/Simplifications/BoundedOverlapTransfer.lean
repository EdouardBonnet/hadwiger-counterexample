import Lax793645Proofs.Simplifications.LinearDensityRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
noncomputable section
variable {A : Type} [Fintype A]

theorem bounded_product_mend (a b d e B : ℝ)
    (ha : 0≤a ∧ a≤B) (hb : 0≤b ∧ b≤B) (hd : 0≤d) (he : 0≤e) :
    a*b≤d*e+B*(|a-d|+|b-e|) := by
  have hB : 0≤B:=ha.1.trans ha.2
  have hbe : b-e≤|b-e|:=le_abs_self _
  by_cases had : d≤a
  · have hdiff : 0≤a-d:=sub_nonneg.mpr had
    have hh : (a-d)*b≤(a-d)*B:=mul_le_mul_of_nonneg_left hb.2 hdiff
    have hi : d*(b-e)≤B*|b-e| :=
      (mul_le_mul_of_nonneg_left hbe hd).trans
        (mul_le_mul_of_nonneg_right (had.trans ha.2) (abs_nonneg _))
    rw [abs_of_nonneg hdiff]
    nlinarith only [hh,hi]
  · have had' : a≤d:=(le_of_not_ge had)
    have hh : a*e≤d*e:=mul_le_mul_of_nonneg_right had' he
    have hi : a*(b-e)≤B*|b-e| :=
      (mul_le_mul_of_nonneg_left hbe ha.1).trans
        (mul_le_mul_of_nonneg_right ha.2 (abs_nonneg _))
    nlinarith only [hh,hi,mul_nonneg hB (abs_nonneg (a-d))]

/-- Only the substitutes are bounded. No bound on either actual density
and no division by a filter or compatibility mass is required. -/
theorem bounded_overlap_transfer (ν d e f g : Wgt A) (hν : ∀ x,0≤ν x)
    (B : ℝ) (hf : ∀ x,0≤f x ∧ f x≤B) (hg : ∀ x,0≤g x ∧ g x≤B)
    (hd : ∀ x,0≤d x) (he : ∀ x,0≤e x) :
    dip ν f g≤dip ν d e+B*(lcost ν f d+lcost ν g e) := by
  have hh:=avg_mono hν (fun x=>bounded_product_mend (f x) (g x) (d x) (e x) B
    (hf x) (hg x) (hd x) (he x))
  simpa only [avg_add,avg_mul',dip,lcost] using hh

theorem bounded_pair_change (ν f g f' g' : Wgt A) (hν : ∀ x,0≤ν x)
    (B : ℝ) (hf' : ∀ x,|f' x|≤B) (hg : ∀ x,|g x|≤B) :
    |dip ν f g-dip ν f' g'|≤B*(lcost ν f f'+lcost ν g g') := by
  unfold dip
  rw [←avg_sub]
  refine (abs_avg_le hν).trans ?_
  have hh x : |f x*g x-f' x*g' x|≤B*(|f x-f' x|+|g x-g' x|) := by
    have he : f x*g x-f' x*g' x=(f x-f' x)*g x+f' x*(g x-g' x):=by ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul]
    have h1:=mul_le_mul_of_nonneg_left (hg x) (abs_nonneg (f x-f' x))
    have h2:=mul_le_mul_of_nonneg_right (hf' x) (abs_nonneg (g x-g' x))
    nlinarith only [h1,h2]
  exact (avg_mono hν hh).trans_eq (by rw [avg_mul',avg_add]; rfl)

end
end Lax793645Proofs.Simplifications
