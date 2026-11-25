import Lax793645Proofs.Simplifications.AffineGradientRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ}

/-- The selector protection budget is independent of selector dimension;
the base protection budget may depend on it, but is independent of n. -/
theorem affine_plan_protection (a : Plan p n) (i : Bool) (q K : ℕ)
    (hK : planRank a ≤ K) :
    ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
      dim U ≤ q*(Fintype.card (Place p)*K) ∧
      dim V ≤ Fintype.card (SelIdx p.b p.j)*(Fintype.card (Place p)*K) ∧
      (∀ z, sPin a z i ≤ tensorCross U V) ∧
      (∀ z x, x ∈ sPin a z i → Matrix.rank (flattenMatrix.symm x) ≤ q →
        x ∈ tensorRectangle U V) := by
  classical
  let P (z : Place p) : Space (Mat (SelIdx p.b p.j) (AIdx p.g n)) :=
    (sPin a z i).map flattenMatrix.symm.toLinearMap
  have hdim (z : Place p) : dim (P z) ≤ K :=
    (Submodule.finrank_map_le _ _).trans ((sPin_dim a z i).trans ((dim_le_plan a z).trans hK))
  have hsum : (∑ z,dim (P z)) ≤ Fintype.card (Place p)*K := by
    simpa using Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hdim z)
  obtain ⟨U,V,hU,hV,hall,hlow⟩ := common_pin_protection P q
  refine ⟨U,V,hU.trans (Nat.mul_le_mul_left _ hsum),
    hV.trans (Nat.mul_le_mul_left _ hsum),?_,?_⟩
  · intro z x hx
    apply (le_sup_right : tensorRectangle ⊤ V ≤ tensorCross U V)
    exact ⟨flattenMatrix.symm x,(box_mem ..).mpr
      ⟨le_top,hall z _ ⟨x,hx,rfl⟩⟩,flattenMatrix.apply_symm_apply x⟩
  intro z x hx hr
  exact ⟨flattenMatrix.symm x,hlow z _ ⟨x,hx,rfl⟩ hr,flattenMatrix.apply_symm_apply x⟩

/-- One common pair of protected spaces can be used for both endpoints. -/
theorem affine_common_plan_protection (a : Plan p n) (q K : ℕ)
    (hK : planRank a ≤ K) :
    ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
      dim U ≤ q*(Fintype.card (Bool × Place p)*K) ∧
      dim V ≤ Fintype.card (SelIdx p.b p.j)*(Fintype.card (Bool × Place p)*K) ∧
      (∀ i z,sPin a z i ≤ tensorCross U V) ∧
      (∀ i z x,x ∈ sPin a z i → Matrix.rank (flattenMatrix.symm x) ≤ q →
        x ∈ tensorRectangle U V) := by
  classical
  let P (z : Bool × Place p) : Space (Mat (SelIdx p.b p.j) (AIdx p.g n)) :=
    (sPin a z.2 z.1).map flattenMatrix.symm.toLinearMap
  have hdim (z : Bool × Place p) : dim (P z) ≤ K :=
    (Submodule.finrank_map_le _ _).trans
      ((sPin_dim a z.2 z.1).trans ((dim_le_plan a z.2).trans hK))
  have hsum : (∑ z,dim (P z)) ≤ Fintype.card (Bool × Place p)*K := by
    simpa using Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hdim z)
  obtain ⟨U,V,hU,hV,hall,hlow⟩ := common_pin_protection P q
  refine ⟨U,V,hU.trans (Nat.mul_le_mul_left _ hsum),
    hV.trans (Nat.mul_le_mul_left _ hsum),?_,?_⟩
  · intro i z x hx
    apply (le_sup_right : tensorRectangle ⊤ V ≤ tensorCross U V)
    exact ⟨flattenMatrix.symm x,(box_mem ..).mpr
      ⟨le_top,hall (i,z) _ ⟨x,hx,rfl⟩⟩,flattenMatrix.apply_symm_apply x⟩
  intro i z x hx hr
  exact ⟨flattenMatrix.symm x,hlow (i,z) _ ⟨x,hx,rfl⟩ hr,flattenMatrix.apply_symm_apply x⟩

end
end Lax793645Proofs.Simplifications
