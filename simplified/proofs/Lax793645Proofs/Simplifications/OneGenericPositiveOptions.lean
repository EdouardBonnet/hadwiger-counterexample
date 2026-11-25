import Lax793645Proofs.Simplifications.OnePositiveOptions
import Lax793645Proofs.Simplifications.OneGenericPopulationScores
import Lax793645Proofs.Simplifications.OnePopulationScores
import Lax793645Proofs.Simplifications.OneScalarOptions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K r:ℕ} {d e:Rates}

namespace OneStation
variable {pop:OneLeafMixture p n N}

theorem inform_generic_options (v:OneStation p n N K pop) (m:Mixer p n)
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
      (oneWake p Y m j.2 (v.cAxes j.1 (toRates e))) (g x).1 x.1 (g x).2)
    (hgeneric : ∀ x side,(g x).1.f side=Flavor.full):
    v.genericEligiblePair m i j Y a := by
  let z:=g.binding p F G
  let I:OneScrip p K:=⟨(q,d,e),k,z⟩
  refine ⟨I,⟨hT.1,⟨fun x=>hgeneric x true,fun x=>hgeneric x false⟩⟩,?_⟩
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
