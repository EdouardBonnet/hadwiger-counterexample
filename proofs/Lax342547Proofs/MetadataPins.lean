import Lax342547.MetadataPins
import Lax342547Proofs.ExactPins
import Lax342547Proofs.FiniteLinearLaw

namespace Lax342547Proofs.MetadataPins

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.MetadataPins

/--
---
conclusion: Lax342547.MetadataPins.image_count
---
Each binary linear map is determined by the images of a basis. Multiplying
over the component/sign spaces adds their dimensions in the exponent.
-/
theorem image_count {Axis I N : Type} [Fintype Axis] [Fintype I] [Fintype N]
    (S : Axis → Submodule Binary (I → Binary)) :
    Nat.card (Images N S) = 2 ^ ((∑ a, Module.finrank Binary (S a)) * Fintype.card N) := by
  classical
  change Nat.card (∀ a, S a →ₗ[Binary] (N → Binary)) = _
  rw [Nat.card_pi]
  have hc (a : Axis) : Nat.card (S a →ₗ[Binary] (N → Binary)) =
      2 ^ (Module.finrank Binary (S a) * Fintype.card N) := by
    let : Finite (S a →ₗ[Binary] (N → Binary)) :=
      Finite.of_injective (fun f : S a →ₗ[Binary] (N → Binary) => (f : S a → N → Binary))
        DFunLike.coe_injective
    let : Fintype (S a →ₗ[Binary] (N → Binary)) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, FiniteLinearLaw.binary_card,
      Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card]
  simp_rw [hc]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_mul]

/--
---
conclusion: Lax342547.MetadataPins.key_count
---
Sum the image-assignment count over all coefficient and scalar metadata
choices. The uniform direction budget gives the stated total count.
-/
theorem key_count {J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (S : J → Axis → Submodule Binary (I → Binary)) (u : ℕ)
    (hu : ∀ j, ∑ a, Module.finrank Binary (S j a) ≤ u) :
    Nat.card (Key N S) ≤ Fintype.card J * 2 ^ (u * Fintype.card N) := by
  change Nat.card (Σ j, Images N (S j)) ≤ _
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _j : J, 2 ^ (u * Fintype.card N) := by
      apply Finset.sum_le_sum
      intro j _
      rw [image_count]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (hu j))
    _ = _ := by simp

theorem mem_record_event {Ω J Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (o : Ω) :
    o ∈ (pin (record A choice S o)).event A := by
  intro a v
  rfl

theorem fiber_subset_event {Ω J Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (o : Ω) :
    {x | record A choice S x = record A choice S o} ⊆ (pin (record A choice S o)).event A := by
  intro x hx
  have h := mem_record_event A choice S x
  rwa [hx] at h

/--
---
conclusion: Lax342547.MetadataPins.refined_fiber
---
The split record fixes a new exact pin event. Join it to the old pins at
one consistent point; quotient dimension cannot exceed the new direction
budget, and the whole fiber satisfies the joined prescriptions.
-/
theorem refined_fiber {Ω J Axis I N : Type} [Fintype Axis] [Fintype I]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (u : ℕ)
    (hu : ∀ j, ∑ a, Module.finrank Binary (S j a) ≤ u)
    (P₀ : Pin Axis I N) (R : Set Ω) (hR : R ⊆ P₀.event A) (o : Ω) (ho : o ∈ R) :
    ∃ P : Pin Axis I N, P₀.Extends P ∧ (pin (record A choice S o)).Extends P ∧
      P.rank ≤ P₀.rank + u ∧
      R ∩ {x | record A choice S x = record A choice S o} ⊆ P.event A := by
  let Q := pin (record A choice S o)
  have he := ExactPins.event_refinement A P₀ Q o ⟨hR ho, mem_record_event A choice S o⟩
  refine ⟨P₀.joinAt A Q o, he.1, he.2.1, ?_, ?_⟩
  · rw [ExactPins.rank_refinement]
    apply Nat.add_le_add_left
    calc
      P₀.relativeRank Q ≤ Q.rank := by
        apply Finset.sum_le_sum
        intro a _
        exact Submodule.finrank_map_le (P₀.space a).mkQ (Q.space a)
      _ ≤ u := hu (choice o)
  · rw [he.2.2]
    exact fun x hx => ⟨hR hx.1, fiber_subset_event A choice S o hx.2⟩

end Lax342547Proofs.MetadataPins
