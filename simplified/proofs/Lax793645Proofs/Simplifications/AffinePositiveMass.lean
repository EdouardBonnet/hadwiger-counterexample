/- Adapted from OpenAI's PositiveTestMass (Apache-2.0). -/
import Lax793645Proofs.Simplifications.AffineFiniteComparison
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function Filter Finset LinearMap Module Template StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p:Shape} {n N K M s0 r :ℕ}
set_option maxHeartbeats 1400000 in
theorem inform_options (w:LeafMixture p n N) (v:Station p n N K w)
    (m:Mixer p n) (Y:Silhouette p N r) (i j:Aspect p n N w)
    (hc:PreparationParameters.frameSide p m i.2) (he:PreparationParameters.frameSide p m j.2)
    (ha:(w.pin i.1.val).agree i.2) (hb:(w.pin j.1.val).agree j.2)
    (d e:Stakes K) {η a:ℝ} (h : supportBudget p K η a) (hη:0<η)
    (k:Fin (2^deckMax p K))
    (hk:berthTicket (w.pin i.1.val) (w.pin j.1.val) (v.mails i.1 j.1 k) (i.2,j.2))
    (q : Volumes) (g : Engagement p (toFormat q) (toRates d) (toRates e))
    (F G : Script p (Messenger (toFormat q)))
    (hT : chances (g.binding p F G) (v.cAxes i.1 (toRates d)) (v.cAxes j.1 (toRates e))
      (w.pin i.1.val) (w.pin j.1.val) (v.mails i.1 j.1 k) K)
    (hU : ∀ z : Messenger (toFormat q),η ≤ circlet (wisp p Y)
      (wake p Y m i.2 (v.cAxes i.1 (toRates d))) (wake p Y m j.2 (v.cAxes j.1 (toRates e)))
      (g z).1 z.1 (g z).2) :
    eligiblePair v m i j Y a := by
  classical
  let X := v.cAxes i.1 (toRates d)
  let W := v.cAxes j.1 (toRates e)
  let z:=g.binding p F G
  let I:Scrip p K:=⟨(q,d,e),k,z⟩
  refine ⟨I,hT.1,?_⟩
  obtain ⟨hL,hR⟩:= berth_flags _ _ _ hk ha hb
  have hC :
      frontPage v z m i.1 j.1 k i.2∧backPage v z m i.1 j.1 k j.2 :=
    ⟨⟨hT,ha,hc,hL⟩,⟨hT,hb,he,hR⟩⟩
  change _≤ ind _ * z.constellation i.2 j.2 X W m Y
  rw [ind_one hC,one_mul]
  refine (h.2 I).trans (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (kappa_pos _).le (kappa_pos _).le))
  let J:=Messenger (toFormat q)
  have hi (x:J):η ≤ z.chimera i.2 j.2 X W m Y x := (hU x).trans_eq
    (Engagement.solicit ..).symm
  exact le_trans (le_of_eq (show η^Fintype.card J=∏ _:J,η by simp)) (Finset.prod_le_prod
    (fun i _=> hη.le) fun i _=> hi i)

end AffineOptions
end
end Lax793645Proofs.Simplifications
