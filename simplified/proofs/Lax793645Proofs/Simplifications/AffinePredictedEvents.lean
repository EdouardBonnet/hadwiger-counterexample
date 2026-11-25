import Lax793645Proofs.Simplifications.AffineHistogramBounds
import Lax793645Proofs.Simplifications.AffinePredictedHits
import Lax793645Proofs.Simplifications.AffineAsymptotics

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p : Shape} {q : Format} {d e : Rates} {side : Bool} {n N K : ℕ}

theorem sales_mono_filter (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q → F) (s : Charts p n d) (m : Mixer p n)
    (pin : Pin p n N) (K : ℕ) (μ : Wgt (UnitType p n N))
    (P Q : UnitType p n N → Prop) (hμ : ∀ x,0 ≤ μ x) (hPQ : ∀ o,P o → Q o) :
    ∀ k,sales w t z pin K μ P m s k ≤ sales w t z pin K μ Q m s k := by
  intro k
  apply avg_mono (prodW_nonneg fun _ => normW_nonneg (subW_nonneg (spins_law ..).nz _))
  exact fun x => pr_mono hμ (fun o ho => ⟨⟨hPQ o ho.1.1,ho.1.2⟩,ho.2⟩)

variable {s : LeafMixture p n N} (v : Station p n N K s) (x : Typus p q d e)
    (m : Mixer p n) (k : Fin (2^deckMax p K)) (μ : Wgt (UnitType p n N))

def predictedCharter (a : ℝ) (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E : Keys (p:=p) x.t N → Prop) (i : s.T × s.T) : Prop :=
  x.permission ∧ ∃ (P Q : UnitType p n N → Prop),
    (∀ o,P o → frontPage v x m i.1 i.2 k o) ∧
    (∀ o,Q o → backPage v x m i.1 i.2 k o) ∧
    x.qA.predictedQualified x.t x.z (v.cAxes i.1 d) m K (partW μ i.1.val) P a α g ε E ∧
    x.qB.predictedQualified x.t x.z (v.cAxes i.2 e) m K (partW μ i.2.val) Q a α g ε E

def predictedBerth (a : ℝ) (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E : Keys (p:=p) x.t N → Prop) : ℝ :=
  pr (pairW (portionW μ s.T) (portionW μ s.T))
    (predictedCharter v x m k μ a α g ε E)

end AffineOptions
end
end Lax793645Proofs.Simplifications
