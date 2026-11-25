import Lax793645Proofs.Simplifications.OneQueryFilteredComparison
import Lax793645Proofs.Simplifications.PrintedStatusComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}

/-- The scalar status vocabulary is unchanged; its parity coordinate now
comes from the single quadratic frame and its opposite channels. -/
def onePrinted (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q→Label p.b) (f : Messenger q→Flavor p.g) (m : Mixer p n)
    (o : OneUnit p n N) (x : Inputs p n (Messenger q)) : Amounts p q d b :=
  joinPrinted (nominalPrinted b v t s f m x) (oneQueryPValues (manager b t s f) o x)

theorem one_printed_status_comparison (b : Bool) (t : Tagging p (Messenger q))
    (s : Messenger q→Label p.b) (f : Messenger q→Flavor p.g)
    [DecidableEq (KeySlots p t)] (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (z : Messenger q→F) (D : Wgt (KeyCoordinates (KeySlots p t) (M*n)))
        (ψ : Wgt (Inputs p n (Messenger q))) (π : Wgt (OneUnit p n (M*n))),
      IsLaw π → (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → oneOwnPart t z x) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      ∀ (v : Charts p n d) (F : OneUnit p n (M*n)→Amounts p q d b→ℝ),
      (∀ o a,|F o a|≤1) →
      avg π (fun o=>|avg unif (fun x=>D (oneTemplateCoordinates (manager b t s f) o x)*ψ x*
        F o (onePrinted b v t s f m o x))|)≤ε := by
  haveI : Nonempty (NominalAmounts p q d b):=⟨fun _=>(0,0)⟩
  obtain ⟨δ,hδ,hcal⟩:=one_capped_filtered_comparison (A:=NominalAmounts p q d b)
    (manager b t s f) M hM c ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal] with n hn m hN z D ψ π hπ hcap hD hsup hFour hψ v F hF
  exact hn m hN z D ψ π hπ hcap hD hsup hFour hψ (nominalPrinted b v t s f m)
    (fun o a r=>F o (joinPrinted a r)) (fun o a r=>hF o _)

end
end Lax793645Proofs.Simplifications
