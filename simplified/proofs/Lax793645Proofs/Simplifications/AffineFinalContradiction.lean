/- Adapted from OpenAI's FinalContradiction (Apache-2.0). -/
import Lax793645Proofs.Simplifications.AffineForbiddenPredictions
import Lax793645Proofs.Simplifications.AffinePredictedEnds
import Lax793645Proofs.Simplifications.LinearPreparation
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FinalContradiction
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Matrix Finset Module LinearMap Function Template StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p:Shape} {n N M r s0:ℕ} {w:rhythms p M}
    {m:cycleM p} {u:tale p M} {b:PreparationParameters} {l:Filter ℕ}
private theorem haveLeads (h:AffineVeil p M b s0 l m w u) :
    ∀ᶠ n in l,Lead (u n) (w n) (m n) b:= by
  filter_upwards [h.durableS.shape,h.moment,h.durableS.mass.positive] with n hn ht hh
  exact ⟨hn.1,hh,ht.1.law,hn.2⟩

set_option maxHeartbeats 1200000 in
theorem quietEnd (v:Stations p M b.pins w) (h:AffineVeil p M b s0 l m w u)
    (ht:∀ᶠ n in l,(v n).bank) (hs:l.NeBot)
    (hq:linearSilenceOutcome b l p M m u w) : False := by
  classical
  obtain ⟨τ,hτ,hQ⟩:=hq
  let K:=b.pins
  obtain ⟨ε,η,he,hM,hC⟩:= cheapFest p K (τ/20) (by positivity)
  obtain ⟨a,hp⟩:= engagedBudget p K hC.pos
  obtain ⟨r,coords,d,hr⟩:=lightmap v h a ε (1/16) hp.1 he (by norm_num) 1
    (fun _ _ _ _=>0)
  have hF:∀ᶠ n in l, False := by
    filter_upwards [hr,hQ,ht,h.upright,haveLeads h,
      (eventually_ge_atTop (8*p.g*coords)).filter_mono h.timeL]
      with n hn hq ht hi hx hcoords
    obtain ⟨X,_,hXlinear,hE⟩:=hn
    have hXL : LinearSilhouette X coords := by
      simpa only [Nat.add_zero] using hXlinear 0 (linear_silhouette_constant (fun _ _=>0))
    exact no_out (w n) b (m n) X (u n) _ _ _ _ _ τ hx ht h.easel hi.age hC he hp hE
      hXL (by linarith only [hM]) (fun h=>hq.1 ⟨coords,hcoords,h⟩) hq.2
  exact hF.exists.elim (fun _ hi=>hi)
theorem refuteVeil (h:AffineVeil p M b s0 l m w u) (hs:l.NeBot)
    (hT:linearSilenceOutcome b l p M m u w ∨ linearPredOutcome b l p M m u w) :
    False := by
  classical
  have he :
      ∀ᶠ n in l, ∃ s:Station p n (M*n) b.pins (w n),s.bank := by
    filter_upwards [h.durableS.shape] with n hn
    exact Station.create (fun x=>(hn.1.leaf _ x.property).bound)
  obtain ⟨s,hq⟩:= taking he
  rcases hT with hP|⟨b,_hlinear,hf,hR|hR⟩
  · exact quietEnd s h hq hs hP
  · exact predicted_gold_end s h hq hs b hf hR
  exact predicted_dim_end s h hq hs b hf hR
end AffineOptions
end
end Lax793645Proofs.Simplifications
