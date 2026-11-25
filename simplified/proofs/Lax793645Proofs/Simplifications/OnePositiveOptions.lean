import Lax793645Proofs.Simplifications.OnePopulationScores
import Lax793645Proofs.Simplifications.OneScalarOptions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K r:ℕ} {d e:Rates}

theorem one_reflected_sub_law {p : Shape} {n N d r : ℕ}
    (x : Appearance p) (Y : OneSilhouette p N r) (i : Nodes) (o : OneUnit p n N)
    (m : Mixer p n) (v : Ax p n d) (c : Fin r) :
    SubLaw (OneAppearance.oneReflected x Y i o m v c) := by
  have hx : SubLaw (x.wit n) := by
    unfold Appearance.wit scopedBit spins
    rw [←draws_unif,on_unif]
    exact unifOn_sub _
  unfold OneAppearance.oneReflected
  apply mapW_sub
  unfold stained
  split
  · exact normW_subLaw (subW_nonneg hx.nz _)
  · exact hx


/-- Every probability-weighted status overlap is bounded by the overlap
of its support indicators. This holds even for an empty query law. -/
theorem one_engagement_support {q:Format} (g:Engagement p q d e)
    (a b:Script p (Messenger q)) (Y:OneSilhouette p N r)
    (X:Charts p n d) (Z:Charts p n e) (m:Mixer p n)
    (o o':OneUnit p n N) (i:Messenger q):
    circlet (oneWisp p Y) (oneWake p Y m o X) (oneWake p Y m o' Z) (g i).1 i.1 (g i).2 ≤
      OneTypus.oneSupportChimera (g.binding p a b) o o' X Z m Y i := by
  let w:=g.binding p a b
  let H:=g i
  let μ:=oneLawOmega p N H.1.l H.1.q
  let u:=Y H.1.l H.1.q
  let F:=couplePage (oneWake p Y m o X) (oneWake p Y m o' Z) H.1 i.1
  change avg (mapW μ u) (fun i=>F i H.2)≤_
  rw [mapW_avg]
  apply avg_mono (map_nz (unifOn_sub _).nz _)
  intro k
  have hA:=one_reflected_sub_law (w.qA.allure w.t w.z i) Y (parcel true i) o m
    (X (parcel true i)) (Y (w.t i) (w.z i) k)
  have hB:=one_reflected_sub_law (w.qB.allure w.t w.z i) Y (parcel false i) o' m
    (Z (parcel false i)) (Y (w.t i) (w.z i) k)
  have hA' : 0≤OneQuill.oneSeraph w.qA w.t w.z o m X Y i k ∧
      OneQuill.oneSeraph w.qA w.t w.z o m X Y i k≤1 :=
    ⟨hA.nz _,(weight_le_tot hA.nz _).trans hA.total⟩
  have hB' : 0≤OneQuill.oneSeraph w.qB w.t w.z o' m Z Y i k ∧
      OneQuill.oneSeraph w.qB w.t w.z o' m Z Y i k≤1 :=
    ⟨hB.nz _,(weight_le_tot hB.nz _).trans hB.total⟩
  have h₁:=support_lower_covers 1 _ zero_le_one hA'
  have h₂:=support_lower_covers 1 _ zero_le_one hB'
  rw [one_mul] at h₁ h₂
  exact mul_le_mul h₁ h₂ hB'.1 (support_lower_bounds 1 _ ⟨zero_le_one,le_rfl⟩).1

namespace OneStation
variable {pop:OneLeafMixture p n N}

theorem inform_options (v:OneStation p n N K pop) (m:Mixer p n)
    (Y:OneSilhouette p N r) (i j:OneAspect pop)
    (hc:oneFrameSide m i.2) (he:oneFrameSide m j.2)
    (ha:imagePinAgree oneCoordinateImages (pop.pin i.1.val) i.2)
    (hb:imagePinAgree oneCoordinateImages (pop.pin j.1.val) j.2)
    (d e:Stakes K) {η a:ℝ} (h:oneSupportBudget p K η a) (hη:0<η)
    (k:Fin (2^oneDeckMax p K))
    (hk:OneOptions.ticket (pop.pin i.1.val) (pop.pin j.1.val) (v.mails i.1 j.1 k) i.2 j.2)
    (q:Volumes) (g:Engagement p (toFormat q) (toRates d) (toRates e))
    (F G:Script p (Messenger (toFormat q)))
    (hT:OneOptions.chances (g.binding p F G) (v.cAxes i.1 (toRates d))
      (v.cAxes j.1 (toRates e)) (pop.pin i.1.val) (pop.pin j.1.val) (v.mails i.1 j.1 k) K)
    (hU:∀ x:Messenger (toFormat q),η≤circlet (oneWisp p Y)
      (oneWake p Y m i.2 (v.cAxes i.1 (toRates d)))
      (oneWake p Y m j.2 (v.cAxes j.1 (toRates e))) (g x).1 x.1 (g x).2):
    v.eligiblePair m i j Y a := by
  let z:=g.binding p F G
  let I:OneScrip p K:=⟨(q,d,e),k,z⟩
  refine ⟨I,hT.1,?_⟩
  obtain ⟨hL,hR⟩:=OneOptions.ticket_flags _ _ _ _ _ hk ha hb
  have hC:v.frontPage z m i.1 j.1 k i.2 ∧ v.backPage z m i.1 j.1 k j.2:=
    ⟨⟨hT,ha,hc,hL⟩,⟨hT,hb,he,hR⟩⟩
  change _ ≤ ind _*OneTypus.oneSupportConstellation z i.2 j.2 _ _ m Y
  rw [ind_one hC,one_mul]
  refine (h.2 I).trans (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (one_kappa_pos _).le (one_kappa_pos _).le))
  let J:=Messenger (toFormat q)
  have hi (x:J):η≤OneTypus.oneSupportChimera z i.2 j.2 _ _ m Y x:=
    (hU x).trans (one_engagement_support ..)
  exact (le_of_eq (show η^Fintype.card J=∏ _:J,η by simp)).trans
    (Finset.prod_le_prod (fun i _=>hη.le) (fun i _=>hi i))

end OneStation
end
end Lax793645Proofs.Simplifications
