import Lax342547.PrimalRetractions

namespace Lax342547Proofs.PrimalRetractions

open Lax342547.MomentSpace

variable {V : Type} [AddCommGroup V] [Module Binary V]

theorem preserving_retraction (S U : Submodule Binary V) (hspan : S ⊔ U = ⊤) :
    ∃ p : V →ₗ[Binary] V, (∀ v, p v ∈ S) ∧ (∀ v ∈ S, p v = v) ∧
      ∀ v ∈ U, p v ∈ U := by
  let q : U →ₗ[Binary] V ⧸ S := S.mkQ.comp U.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    have hv : v ∈ S ⊔ U := by rw [hspan]; trivial
    obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨u, hu⟩, ?_⟩
    have hs0 : S.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hs
    simp [q, map_add, hs0]
  obtain ⟨lift, hlift⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let p : V →ₗ[Binary] V := LinearMap.id - (U.subtype.comp lift).comp S.mkQ
  refine ⟨p, ?_, ?_, ?_⟩
  · intro v
    apply (Submodule.Quotient.mk_eq_zero S).mp
    change S.mkQ (p v) = 0
    change S.mkQ (v - (lift (S.mkQ v)).val) = 0
    rw [map_sub]
    have he : S.mkQ (lift (S.mkQ v)).val = S.mkQ v := DFunLike.congr_fun hlift (S.mkQ v)
    rw [he, sub_self]
  · intro v hv
    have hz : S.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hv
    simp [p, hz]
  · intro v hv
    exact U.sub_mem hv (lift (S.mkQ v)).property

/--
---
conclusion: Lax342547.PrimalRetractions.bounded_retraction
---
The primal space surjects onto the quotient by table plus keys. Choose a
linear section of that surjection and subtract its lifted quotient map
from the identity. The resulting retraction preserves the primal space.
Its primal range lies in the intersection with table plus keys, whose
dimension is at most the table-primal dimension plus the key dimension.
-/
theorem bounded_retraction [FiniteDimensional Binary V] (J Keys U : Submodule Binary V)
    (hspan : J ⊔ U = ⊤) (hKeys : Keys ≤ U) :
    ∃ p : V →ₗ[Binary] V,
      (∀ v, p v ∈ J ⊔ Keys) ∧ (∀ v ∈ J ⊔ Keys, p v = v) ∧
      (∀ v ∈ U, p v ∈ U) ∧
      Module.finrank Binary (LinearMap.range (p.comp U.subtype)) ≤
        Module.finrank Binary ↥(J ⊓ U) + Module.finrank Binary Keys := by
  have hs : (J ⊔ Keys) ⊔ U = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  obtain ⟨p, hp, hfix, hU⟩ := preserving_retraction (J ⊔ Keys) U hs
  refine ⟨p, hp, hfix, hU, ?_⟩
  have hrange : LinearMap.range (p.comp U.subtype) ≤ (J ⊔ Keys) ⊓ U := by
    rintro _ ⟨v, rfl⟩
    exact ⟨hp v.val, hU v.val v.property⟩
  calc
    _ ≤ Module.finrank Binary ↥((J ⊔ Keys) ⊓ U) := Submodule.finrank_mono hrange
    _ = Module.finrank Binary ↥((J ⊓ U) ⊔ Keys) := by
      rw [sup_comm J Keys, sup_inf_assoc_of_le J hKeys, sup_comm]
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

end Lax342547Proofs.PrimalRetractions
