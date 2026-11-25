import Lax793645Proofs.Simplifications.OneAnalyticAsymptotics
import Lax793645Proofs.Simplifications.OneBaseProductHits

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure OneAlign (q:PreparationParameters) (p:Shape) (M n s0:ℕ)
    (m:Mixer p n) (u:Wgt (OneUnit p n (M*n))):Prop where
  law:IsLaw u
  border:oneBySide u m (bp ((1/32:ℝ)*n))
  cap:∀ x,u x≤bp (q.spJoint*(2*(M*n):ℝ))*oneUnitRaw m (M*n) x
  age:2*p.r≤n
  cols:Fintype.card (Row p n)+2*p.h+3≤M*n
  unary:unaryGood m (onePreparationPins q) s0
  binary:reducedBinaryGood m

theorem OneVeil.upright {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
    {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}
    (h:OneVeil p M q s0 l m s w):
    ∀ᶠ n in l,OneAlign q p M n s0 (m n) ((s n).sap (w n)) := by
  filter_upwards [h.query_caps,h.parameters.planted.unary_room.filter_mono h.time,h.moment,
    (eventually_ge_atTop (2*p.r)).filter_mono h.time] with n hc hr hm ha
  exact ⟨hc.1,hc.2.1,hc.2.2,ha,hr,hm.2.1,hm.2.2.1⟩

namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {side:Bool} {M s0:ℕ} {b:PreparationParameters}

theorem one_aligned_relative_hit (w:Quill p q d side) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (hw:w.moral t z) (h:OneAnalyticParameters p M b s0)
    (paints:ℕ) (ε:ℝ) (hε:0<ε):
    ∃ c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n (M*n))),OneAlign b p M n s0 m u →
      ∀ H:OneKeys t (M*n)→Prop,OneDesign t (fun x=>ind (H x)) paints →
      ε≤pr (oneLawNu p (M*n) t z) H →
      pr u (fun o=>¬OneBaseSober w t z (onePreparationPins b) H m
        (oneDilate w t (onePreparationPins b)*(pr (oneLawNu p (M*n) t z) H/4)) o)
        ≤bp (-c*n) := by
  obtain ⟨c,hc,hcal⟩:=one_base_product_relative_hit w t z hw M h.unary h.thickness b.spJoint paints ε hε
  refine ⟨c,hc,?_⟩
  filter_upwards [hcal] with n hn m u hu H hD hH
  exact hn m u hu.law hu.border (by simpa only [Nat.cast_mul] using hu.cap)
    hu.cols hu.unary hu.binary H hD hH

theorem one_aligned_base_hit (w:Quill p q d side) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (hw:w.moral t z) (h:OneAnalyticParameters p M b s0)
    (paints:ℕ) (ε:ℝ) (hε:0<ε):
    ∃ c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n (M*n))),OneAlign b p M n s0 m u →
      ∀ H:OneKeys t (M*n)→Prop,OneDesign t (fun x=>ind (H x)) paints →
      ε≤pr (oneLawNu p (M*n) t z) H →
      pr u (fun o=>¬OneBaseSober w t z (onePreparationPins b) H m (oneDilate w t (onePreparationPins b)*(ε/4)) o)
        ≤bp (-c*n) := by
  obtain ⟨c,hc,hcal⟩:=one_base_product_hit_gain w t z hw M h.unary h.thickness b.spJoint paints ε hε
  refine ⟨c,hc,?_⟩
  filter_upwards [hcal] with n hn m u hu H hD hH
  exact hn m u hu.law hu.border (by simpa only [Nat.cast_mul] using hu.cap)
    hu.cols hu.unary hu.binary H hD hH

end OneQuill
end
end Lax793645Proofs.Simplifications
