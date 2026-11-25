import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectedSurrogates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section

/-- Only failure of domination costs anything. Excess actual mass is
harmless, even when the actual densities are unbounded. -/
theorem one_sided_product_mend (a b c d : ℝ)
    (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) (hc : 0≤c) (hd : 0≤d) :
    a*b≤c*d+max (a-c) 0+max (b-d) 0 := by
  by_cases hac : c≤a
  · rw [max_eq_left (sub_nonneg.mpr hac)]
    have h1 : (a-c)*b≤a-c:=by nlinarith only [mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hb.2)]
    have h2 : c*(b-d)≤max (b-d) 0 := by
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hc).trans
        (by nlinarith only [mul_nonneg (sub_nonneg.mpr (hac.trans ha.2)) (le_max_right (b-d) 0)])
    nlinarith only [h1,h2]
  · have hac' : a≤c:=le_of_not_ge hac
    rw [max_eq_right (sub_nonpos.mpr hac')]
    have h1 : a*d≤c*d:=mul_le_mul_of_nonneg_right hac' hd
    have h2 : a*(b-d)≤max (b-d) 0 := by
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.1).trans
        (by nlinarith only [mul_nonneg (sub_nonneg.mpr ha.2) (le_max_right (b-d) 0)])
    nlinarith only [h1,h2]

variable {A B : Type} [Fintype A] [Fintype B]

theorem one_sided_projected_mend (ν : Wgt A) (hν : IsLaw ν) (P : A→B)
    (f g d e : Wgt A) (hf : bower f) (hg : bower g)
    (hd : ∀ x,0≤d x) (he : ∀ x,0≤e x) :
    dip ν f g^2≤dip ν (banner ν P d) (banner ν P e)+
      avg ν (fun x=>max (banner ν P f x-banner ν P d x) 0)+
      avg ν (fun x=>max (banner ν P g x-banner ν P e x) 0) := by
  have h1:=garden ν f P hν hf
  have h2:=garden ν g P hν hg
  have hh:=avg_mono hν.nz (fun x=>one_sided_product_mend
    (banner ν P f x) (banner ν P g x) (banner ν P d x) (banner ν P e x)
    ⟨h1.1 x,h1.2 x⟩ ⟨h2.1 x,h2.2 x⟩
    (book_nonneg ν P hν d hd (P x)) (book_nonneg ν P hν e he (P x)))
  rw [avg_add,avg_add] at hh
  exact (projected_min ν P hν f g hf hg).trans hh

end
end Lax793645Proofs.Simplifications
