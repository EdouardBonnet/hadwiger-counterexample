/- Adapted from OpenAI's AdaptiveProjectionBounds (Apache-2.0). -/
import Lax793645Proofs.Simplifications.AffineKeyProjection
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AdaptiveProjectionBounds
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Finset Matrix StatusAnalysis Station PreparationParameters
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p:Shape} {n N K M r z s0:ℕ} {q:Format} {d e:Rates} {b:Bool}
variable {w:LeafMixture p n N} (t:Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (k: Fin (2^deckMax p K))
    (μ:Wgt (UnitType p n N)) (Y:Silhouette p N r)
set_option maxHeartbeats 1200000 in
theorem projectSum (P : Keys (p:=p) x.t N→Fin z)
    (h :apart w.T) (hm:IsLaw μ) (hw :∀ i∈w.T,0<partMass μ i) (hs : 0<w.amount μ)
    (ha : ∀ i,IsLaw (x.qA.policies x.t x.z n i)) (hb:∀ i,IsLaw (x.qB.policies x.t x.z n i))
    (hν : IsLaw (lawNu p N x.t x.z)) (ε v v' τ B δ : ℝ) (he:0≤ε)
    (hf : x.permission)
    (ht : τ ≤ v ∧ τ≤v')
    (hh : pr (w.sap μ) (fun i=>¬gauze p τ δ Y m K i)≤B)
    (hx : ∀ i:Fin z,pr (w.sap μ) (x.qA.flunk x.t x.z Y (fun y=>ind (P y=i)) m v ε)≤B)
    (hy : ∀ i:Fin z,pr (w.sap μ) (x.qB.flunk x.t x.z Y (fun y=>ind (P y=i)) m v' ε)≤B) :
    due t x m μ k Y P≤2*(z*(ε+2*(B+B))) := by
  classical
  obtain ⟨hp,hq⟩:=rebuild hm.nz h hw hs
  let A (i:w.T):=partW μ i.val
  let u:=portionW μ w.T
  have hQ : w.sap μ=mixW u A :=hq
  let V:=pairW u u; have hA i:IsLaw (A i):=on_law hm.nz (hw i.val i.property)
  have hL : avg V (fun i=> taxLeft t x m μ k Y P i.1 i.2) ≤ z*(ε+2*(B+B)) := by
    refine x.qA.oneTrestle m x.t x.z w Y u hp (fun i=>t.cAxes i d) A hA P
      (fun i=> frontPage t x m i.1 i.2 k) (fun i o h => h.2.2.1) ha hν ε v B B he
      (fun i=>by rw [←hQ]; exact hx i) ?_
    rw [←hQ]; apply (pr_mono (LeafMixture.sapLaw hs hm).nz ?_).trans hh
    exact fun i hi h=> hi (gauzed_area _ _ _ _ hf.2.1 δ ht.1 i h)
  have hR : avg V (fun i=> taxRight t x m μ k Y P i.1 i.2) ≤ z*(ε+2*(B+B)) := by
    refine x.qB.oneTrestle m x.t x.z w Y u hp (fun i=>t.cAxes i e) A hA P
      (fun i=> backPage t x m i.1 i.2 k) (fun i o h => h.2.2.1) hb hν ε v' B B he
      (fun i=>by rw [←hQ]; exact hy i) ?_
    rw [←hQ]; apply (pr_mono (LeafMixture.sapLaw hs hm).nz ?_).trans hh
    exact fun i hi h=>hi (gauzed_area _ _ _ _ hf.2.2.1 δ ht.2 i h)
  unfold due; rw [avg_add,two_mul]
  exact add_le_add hL hR

end AffineOptions
end
end Lax793645Proofs.Simplifications
