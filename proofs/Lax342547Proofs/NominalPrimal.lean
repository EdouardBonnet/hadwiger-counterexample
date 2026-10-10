import Lax342547.NominalPrimal
import Lax342547Proofs.TableSpaces

namespace Lax342547Proofs.NominalPrimal

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces
open Lax342547.NominalPrimal

variable {Comp B H N : Type}

/--
---
conclusion: Lax342547.NominalPrimal.table_spans
---
Split each nominal vector into its channel part, which belongs to the
table, and its primal part. These add to the original vector.
-/
theorem table_spans (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    tableSpace P a ⊔ primal = ⊤ := by
  apply top_unique
  intro v _
  let p : (Fin 2 × (B ⊕ H)) → Binary := fun x => Sum.elim (fun b => v (x.1, Sum.inl b)) (fun _ => 0) x.2
  have hp : p ∈ primal := by intro i h; rfl
  have hc : v - p ∈ tableSpace P a := by
    intro i
    have he : primalProjection i (v - p) = 0 := by ext b; simp [primalProjection, p]
    rw [he]
    exact (projected P i a).zero_mem
  exact Submodule.mem_sup.mpr ⟨v - p, hc, p, hp, sub_add_cancel v p⟩

def primalCoordinates (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    ↥(tableSpace P a ⊓ primal) →ₗ[Binary] ∀ i : Fin 2, projected P i a where
  toFun v i := ⟨primalProjection i v.val, v.property.1 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primalCoordinates_injective (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a : Comp × Bool) : Function.Injective (primalCoordinates P a) := by
  intro v w h
  apply Subtype.ext
  ext ⟨i, b | c⟩
  · exact congrArg (fun f => (f i).val b) h
  · exact (v.property.2 i c).trans (w.property.2 i c).symm

/--
---
conclusion: Lax342547.NominalPrimal.table_primal_dimension
---
Read the two projected primal blocks. On a vector with no channel
coordinates this is injective. Each projected block has dimension at
most the total stored pin rank.
-/
theorem table_primal_dimension [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Module.finrank Binary ↥(tableSpace P a ⊓ primal) ≤ 2 * P.rank := by
  have hd (i : Fin 2) : Module.finrank Binary (projected P i a) ≤ P.rank :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans
      (ProjectedPins.projected_rank P i)
  calc
    _ ≤ Module.finrank Binary (∀ i : Fin 2, projected P i a) :=
      LinearMap.finrank_le_finrank_of_injective (primalCoordinates_injective P a)
    _ = ∑ i : Fin 2, Module.finrank Binary (projected P i a) := Module.finrank_pi_fintype _
    _ ≤ ∑ _i : Fin 2, P.rank := Finset.sum_le_sum (fun i _ => hd i)
    _ = 2 * P.rank := by simp

/--
---
conclusion: Lax342547.NominalPrimal.key_space_bound
---
All generators have zero channel coordinates. The dimension of their
span is at most the size of the indexing family.
-/
theorem key_space_bound {I : Type} [Fintype I] [Fintype B] [Fintype H]
    (endpoint : I → Fin 2) (ray : I → B → Binary) :
    keySpace (H := H) endpoint ray ≤ primal ∧
      Module.finrank Binary (keySpace (H := H) endpoint ray) ≤ Fintype.card I := by
  constructor
  · apply Submodule.span_le.mpr
    rintro v ⟨x, rfl⟩ i h
    simp [primalEmbedding]
  · exact finrank_range_le_card (R := Binary) (fun x => primalEmbedding (H := H) (endpoint x) (ray x))

end Lax342547Proofs.NominalPrimal
