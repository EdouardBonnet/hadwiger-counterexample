import Lax793645Proofs.Simplifications.OneExactForbiddenPredictions
import Lax793645Proofs.Simplifications.OneExactCatalogCalendar

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis StatusAnalysis.DualAnalysis Filter
open scoped Topology
noncomputable section
variable {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}

theorem OneVeil.leads (h:OneVeil p M q s0 l m s w):
    ∀ᶠ n in l,OneLead (w n) (s n) (m n) q.leafNew (2*q.ζ) (onePreparationPins q) := by
  filter_upwards [h.durable.shape,h.moment,h.durable.mass.positive] with n hn ht hh
  exact ⟨hn.1,hh,ht.1.law,hn.2⟩

theorem one_quiet_end (v:OneStations p M (onePreparationPins q) s)
    (h:OneVeil p M q s0 l m s w) (hv:∀ᶠ n in l,(v n).bank) (hl:l.NeBot)
    (hout:oneLinearSilenceOutcome q l m w s):False := by
  classical
  obtain ⟨τ,hτ,hQ⟩:=hout
  let K:=onePreparationPins q
  obtain ⟨ε,η₀,he,_,hC₀⟩:=cheapFest p K 1 zero_lt_one
  let gap:=bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))
  let η:=min η₀ gap
  have hη:η≤gap:=min_le_right _ _
  have hC:Jubilee p K ε η := by
    have hm:playbook p K*η≤playbook p K*η₀ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (playbook_pos _ _).le
    exact ⟨lt_min hC₀.pos (bp_pos _),hm.trans hC₀.book,hm.trans_lt hC₀.sturdyR,hC₀.low⟩
  obtain ⟨a,hp⟩:=one_engaged_budget p K hC.pos
  obtain ⟨r,coords,δ,hr⟩:=one_generic_lightmap v h a ε (1/16) hp.1 he (by norm_num) 1 0
    (fun _ _ _ _=>0) (fun _=>one_full_linear_constant (fun _ _=>0))
  have hF:∀ᶠ n in l,False:=by
    filter_upwards [hr,hQ,hv,h.leads,h.exact_catalog_calendar coords,
      (eventually_ge_atTop (2*p.r)).filter_mono h.time,
      (eventually_ge_atTop (8*p.g*coords)).filter_mono h.time]
      with n hn hq ht hx hcatalog hnR hcoords
    obtain ⟨X,_,hlin,hE⟩:=hn
    obtain ⟨H,hgood,hgap,hnorm,hcontinue,hsep⟩:=hcatalog r X hlin
    exact OneExactOptions.no_out (s n) q (m n) X (w n) (v n) ε η a δ τ hx ht
      h.parameters hnR hC he hp hE hlin.linear hcoords hτ H hgood hgap hnorm hcontinue hη hsep hq.1 hq.2
  exact hF.exists.elim (fun _ hi=>hi)

end
end Lax793645Proofs.Simplifications
