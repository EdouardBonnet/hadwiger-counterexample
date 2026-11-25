import Lax793645Proofs.Simplifications.OneSupportAggregation

/-! Numerical option scores use only intersections of conditional supports. Reference product comparison connects them to bounded surrogates. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace OneTypus
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates}
variable (w : Typus p q d e) (o o' : OneUnit p n N)
  (s : Charts p n d) (t : Charts p n e) (m : Mixer p n) (Y : OneSilhouette p N r)
def oneSupportChimera (i : Messenger q):=
  dip (oneLawOmega p N (w.t i) (w.z i)) (OneQuill.oneSupportSeraph w.qA w.t w.z o m s Y 1 i)
    (OneQuill.oneSupportSeraph w.qB w.t w.z o' m t Y 1 i)
def oneSupportConstellation:=oneMomus w*∏ i,oneSupportChimera w o o' s t m Y i

theorem one_support_shine_match (hN : 2*num (Messenger q×Toast p)+2≤(N:ℝ)) :
    |oneSupportConstellation w o o' s t m Y-
      dip (oneLawNu p N w.t w.z) (OneQuill.oneSupportMirror w.qA w.t w.z o m s Y 1)
        (OneQuill.oneSupportMirror w.qB w.t w.z o' m t Y 1)|≤
      2*quadraticNetFact (trayPort p w.t)*bp (-(N:ℝ)/2) := by
  let A:=OneQuill.oneSupportSeraph w.qA w.t w.z o m s Y 1
  let B:=OneQuill.oneSupportSeraph w.qB w.t w.z o' m t Y 1
  let C (i : Messenger q):=fun x=>A i x*B i x
  have hc i x : |C i x|≤1 := by
    have h₁:=support_lower_bounds 1 (OneQuill.oneSeraph w.qA w.t w.z o m s Y i x) ⟨by norm_num,le_rfl⟩
    have h₂:=support_lower_bounds 1 (OneQuill.oneSeraph w.qB w.t w.z o' m t Y i x) ⟨by norm_num,le_rfl⟩
    dsimp only [C,A,B,OneQuill.oneSupportSeraph]
    rw [abs_mul,abs_of_nonneg h₁.1,abs_of_nonneg h₂.1]
    exact (mul_le_mul h₁.2 h₂.2 h₂.1 zero_le_one).trans_eq (one_mul _)
  have he : dip (oneLawNu p N w.t w.z) (OneQuill.oneSupportMirror w.qA w.t w.z o m s Y 1)
      (OneQuill.oneSupportMirror w.qB w.t w.z o' m t Y 1)=
      oneMomus w*avg (oneLawNu p N w.t w.z) (prodW C) := by
    unfold dip
    rw [←avg_mul']
    apply avg_congr
    intro x _
    simp only [OneQuill.oneSupportMirror,oneMomus,prodW,C,A,B,prod_mul_distrib]
    ring
  have hκ : |oneMomus w|≤1 := by
    rw [oneMomus,abs_mul,abs_of_pos (one_kappa_pos _),abs_of_pos (one_kappa_pos _)]
    exact (mul_le_mul (OneQuill.one_kappa_top w.qA w.t) (OneQuill.one_kappa_top w.qB w.t)
      (one_kappa_pos _).le zero_le_one).trans_eq (one_mul _)
  rw [he]
  change |oneMomus w*(∏ i,avg (oneLawOmega p N (w.t i) (w.z i)) (C i))-
    oneMomus w*avg (oneLawNu p N w.t w.z) (prodW C)|≤_
  rw [←mul_sub,abs_mul]
  exact ((mul_le_mul_of_nonneg_right hκ (abs_nonneg _)).trans_eq (one_mul _)).trans
    (by rw [abs_sub_comm]; exact one_reference_product w.t w.z C hc hN)

end OneTypus

namespace OneTypus
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates}
variable (w : Typus p q d e) (μ ρ : Wgt (OneUnit p n N))
  (F G : OneUnit p n N→Prop) (s : Charts p n d) (t : Charts p n e)
  (m : Mixer p n) (Y : OneSilhouette p N r) (θ : ℝ)

def oneSupportFilteredScore:=avg (pairW μ ρ) (fun o=>ind (F o.1 ∧ G o.2)*oneSupportConstellation w o.1 o.2 s t m Y)

theorem one_support_constellation_nonneg (o o' : OneUnit p n N)
    :
    0≤oneSupportConstellation w o o' s t m Y := by
  apply mul_nonneg (mul_nonneg (one_kappa_pos _).le (one_kappa_pos _).le)
  apply prod_nonneg
  intro i _
  exact avg_nonneg (fun x=>map_nz (unifOn_sub _).nz _ x) (fun x=>mul_nonneg
    (support_lower_bounds 1 (OneQuill.oneSeraph w.qA w.t w.z o m s Y i x) ⟨by norm_num,le_rfl⟩).1
    (support_lower_bounds 1 (OneQuill.oneSeraph w.qB w.t w.z o' m t Y i x) ⟨by norm_num,le_rfl⟩).1)

theorem one_support_showcase_pair :
    dip (oneLawNu p N w.t w.z) (OneQuill.oneSupportShowcase w.qA w.t w.z m s Y μ F 1)
      (OneQuill.oneSupportShowcase w.qB w.t w.z m t Y ρ G 1)=
      avg (pairW μ ρ) (fun o=>ind (F o.1 ∧ G o.2)*
        dip (oneLawNu p N w.t w.z) (OneQuill.oneSupportMirror w.qA w.t w.z o.1 m s Y 1)
          (OneQuill.oneSupportMirror w.qB w.t w.z o.2 m t Y 1)) := by
  change dip _ (mixW μ _) (mixW ρ _)=_
  rw [dip_mixture_product]
  apply avg_congr
  intro o _
  unfold dip
  rw [←avg_mul']
  exact avg_congr (fun x _=>by rw [ind_and]; ring)

theorem one_filtered_support_shine (hμ : IsLaw μ) (hρ : IsLaw ρ)
    (hN : 2*num (Messenger q×Toast p)+2≤(N:ℝ)) :
    |oneSupportFilteredScore w μ ρ F G s t m Y-
      dip (oneLawNu p N w.t w.z) (OneQuill.oneSupportShowcase w.qA w.t w.z m s Y μ F 1)
        (OneQuill.oneSupportShowcase w.qB w.t w.z m t Y ρ G 1)|≤
      2*quadraticNetFact (trayPort p w.t)*bp (-(N:ℝ)/2) := by
  rw [oneSupportFilteredScore,one_support_showcase_pair,←avg_sub]
  apply (abs_avg_le (pairW_law hμ hρ).nz).trans
  apply (pairW_law hμ hρ).avg_le
  intro o
  rw [←mul_sub,abs_mul,abs_of_nonneg (ind_nonneg _)]
  exact ((mul_le_mul_of_nonneg_right (ind_le_one _) (abs_nonneg _)).trans_eq (one_mul _)).trans
    (one_support_shine_match w o.1 o.2 s t m Y hN)



end OneTypus

end
end Lax793645Proofs.Simplifications
