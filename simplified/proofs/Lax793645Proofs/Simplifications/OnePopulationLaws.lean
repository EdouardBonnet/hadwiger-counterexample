import Lax793645Proofs.Simplifications.OnePreparationConditions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PositiveTestMass

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K:ℕ} {C ζ:ℝ}

abbrev OneAspect (pop:OneLeafMixture p n N):=pop.T×OneUnit p n N
abbrev OneViewPair (pop:OneLeafMixture p n N):=OneAspect pop×OneAspect pop

def oneTroupe (pop:OneLeafMixture p n N) (μ:Wgt (OneUnit p n N)):=
  semi (portionW μ pop.T) (fun i=>partW μ i.val)
def oneCirque (pop:OneLeafMixture p n N) (μ:Wgt (OneUnit p n N)):=
  pairW (oneTroupe pop μ) (oneTroupe pop μ)

structure OneLead (μ:Wgt (OneUnit p n N)) (pop:OneLeafMixture p n N)
    (m:Mixer p n) (C ζ:ℝ) (K:ℕ):Prop where
  strength:oneLeafStrength pop μ m C ζ K
  amount:0<pop.amount μ
  law:IsLaw μ
  cover:pop.within (oneFrameSide m)

variable {pop:OneLeafMixture p n N} {μ:Wgt (OneUnit p n N)} {m:Mixer p n}

theorem one_troupe_bill (h:OneLead μ pop m C ζ K):
    IsLaw (oneTroupe pop μ) ∧ mapW (oneTroupe pop μ) Prod.snd=pop.sap μ := by
  obtain ⟨h1,h2⟩:=rebuild h.law.nz h.strength.part
    (fun i hi=>(h.strength.leaf i hi).pos) h.amount
  have hk (i:pop.T):IsLaw (partW μ i.val):=on_law h.law.nz
    (h.strength.leaf i.val i.property).pos
  constructor
  · constructor
    · intro x; exact mul_nonneg (h1.nz _) ((hk _).nz _)
    unfold oneTroupe
    rw [semi_total]
    simp_rw [(hk _).total]
    exact h1.avg_const _
  change _=allW μ pop.T
  rw [h2]
  funext i
  unfold mapW mixW pr oneTroupe
  rw [semi_avg]
  simp_rw [show ∀ j:pop.T,avg (partW μ j.val) (fun x=>ind (x=i))=partW μ j.val i from
    fun j=>pr_point' ..]

theorem one_troupe_home (h:OneLead μ pop m C ζ K) (x:OneAspect pop)
    (hx:oneTroupe pop μ x≠0):
    x.2∈x.1.val ∧ pop.rooting x.2=(pop.pin x.1.val).sp ∧ oneFrameSide m x.2 ∧
      imagePinAgree oneCoordinateImages (pop.pin x.1.val) x.2 := by
  have he:x.2∈x.1.val:=(onW_ne (right_ne_zero_of_mul hx)).1
  exact ⟨he,congrArg ImagePin.sp (pop.poller_eq h.strength.part x.1.property he),
    h.cover _ x.1.property x.2 he,(h.strength.leaf _ x.1.property).fixpin x.2 he⟩

theorem one_cirque_unit (h:OneLead μ pop m C ζ K):
    mapW (oneCirque pop μ) (fun i=>(i.1.2,i.2.2))=pairW (pop.sap μ) (pop.sap μ) := by
  have hk:=map_pair_law (oneTroupe pop μ) (oneTroupe pop μ) Prod.snd Prod.snd
  rw [(one_troupe_bill h).2] at hk
  exact hk

end
end Lax793645Proofs.Simplifications
