/-
Adapted from RelationMismatchBounds (OpenAI,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0).
Generic status positivity supplies the enlarged finite deletion budget;
there is no high-degree interpolation in this argument.
-/
import Lax793645Proofs.Simplifications.ScalableSpanStability
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RelationMismatchBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis StatusAnalysis.Guild StatusAnalysis.Club
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {r K : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e} {β η δ : ℝ}

set_option maxHeartbeats 900000 in
theorem plenitude_at_budget (budget : ℕ) (h:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (hg:3 ≤ p.g) (A B:Stalls p) (hk : ∀ i,(A i).card+budget < Fintype.card (Label p.b))
    (hl : ∀ i,(B i).card+budget < Fintype.card (Label p.b))
    (hβ:0<β) (hz:0<η) (hη : playbook p K*η<1/2*β^2)
    (hd:∀ i,d i≤K^2) (he:∀ i,e i≤K^2):
    richAt (stellar u s t η A B) budget := by
  classical
  intro i S hu y
  have hh a (b:Finset (Label p.b)) (h : b.card+budget<Fintype.card (Label p.b)):
      ∃ z,z∉b∧z∉S a := by
    obtain ⟨z,hz⟩:=any_label (b∪S a) ((card_union_le ..).trans_lt ((Nat.add_le_add_left
      (hu a) _).trans_lt h))
    exact ⟨z,fun ht=>hz (mem_union_left _ ht),fun ht=>hz (mem_union_right _ ht)⟩
  obtain ⟨v,h1,h2⟩:= hh true (A i.1) (hk _)
  obtain ⟨w,h3,h4⟩:= hh false (B i.2) (hl _)
  let x : Zodiac p:= ⟨⟨0,by omega⟩,y.1,fun i=>if i then v else w,fun _=>Flavor.full⟩
  have hh : x.common:= fun i=> generic_apt p hg _ rfl
  obtain ⟨W,hA,hB,hC⟩:= sturdy_contact u s t h hs ht hβ x hh (fun _=>rfl) i y.2.1 y.2.2 hz
    ((mul_le_mul_of_nonneg_right (booklet_cap p K _ _ (hd _) (he _)) hz.le).trans_lt hη)
  refine ⟨(x,W),⟨⟨h1,h3,hA⟩,fun i=>?_⟩,?_⟩
  · cases i; exact h4; exact h2
  exact Prod.ext rfl (Prod.ext hB hC)

end
end Lax793645Proofs.Simplifications
