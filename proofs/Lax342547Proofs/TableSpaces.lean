import Lax342547.TableSpaces
import Lax342547.ProjectedPins

namespace Lax342547Proofs.TableSpaces

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

theorem primalProjection_embedding {B H : Type} (i j : Fin 2) (v : B → Binary) :
    primalProjection (H := H) i (primalEmbedding j v) = if i = j then v else 0 := by
  ext b
  by_cases h : i = j <;> simp [primalProjection, primalEmbedding, h]

theorem primalProjection_channel {B H : Type} (i j : Fin 2) (v : H → Binary) :
    primalProjection (B := B) i (channelEmbedding j v) = 0 := by
  ext b
  simp [primalProjection, channelEmbedding]

/--
---
conclusion: Lax342547.TableSpaces.pin_le_table
---
Each primal projection of a stored pin belongs to the corresponding
projected space, by its defining image witness.
-/
theorem pin_le_table {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    P.space a ≤ tableSpace P a := by
  intro v hv i
  exact ⟨v, hv, rfl⟩

/--
---
conclusion: Lax342547.TableSpaces.table_mono
---
Enlarging stored pins enlarges every primal projection, hence the full
table-coordinate space, while retaining all channel coordinates.
-/
theorem table_mono {Comp B H N : Type}
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (h : P.Extends Q) (a : Comp × Bool) :
    tableSpace P a ≤ tableSpace Q a := by
  intro v hv i
  exact Lax342547.ProjectedPins.projected_mono P Q h i a (hv i)

/--
---
conclusion: Lax342547.TableSpaces.protected_rank
---
Channel projection cannot increase dimension. Sum this inequality over
the component/sign spaces of the fixed endpoint.
-/
theorem protected_rank {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) :
    (∑ a, Module.finrank Binary (protectedChannel P i a)) ≤ P.rank := by
  exact Finset.sum_le_sum (fun a _ => Submodule.finrank_map_le (channelProjection i) (P.space a))

/--
---
conclusion: Lax342547.TableSpaces.private_complement
---
The projected protected channel space has a linear complement in the
channel coordinate space. No orthogonal-complement assumption is made.
-/
theorem private_complement {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (a : Comp × Bool) :
    ∃ U : Submodule Binary (H → Binary), IsCompl (protectedChannel P i a) U :=
  (protectedChannel P i a).exists_isCompl

def coordinateMap {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    tableSpace P a →ₗ[Binary] ∀ i : Fin 2, projected P i a × (H → Binary) where
  toFun v i := (⟨primalProjection i v.val, v.property i⟩, channelProjection i v.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateMap_injective {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Function.Injective (coordinateMap P a) := by
  intro v w h
  apply Subtype.ext
  ext ⟨i, b | c⟩
  · exact congrArg (fun f => (f i).1.val b) h
  · exact congrArg (fun f => (f i).2 c) h

/--
---
conclusion: Lax342547.TableSpaces.table_dimension
---
Read a table vector in its two primal and two channel coordinate blocks.
This map is injective. Each primal projection has dimension at most the
total pin rank, and each channel block has its full coordinate dimension.
-/
theorem table_dimension {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Module.finrank Binary (tableSpace P a) ≤ 2 * P.rank + 2 * Fintype.card H := by
  classical
  have hprimal (i : Fin 2) : Module.finrank Binary (projected P i a) ≤ P.rank :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans
      (Lax342547.ProjectedPins.projected_rank P i)
  calc
    _ ≤ Module.finrank Binary (∀ i : Fin 2, projected P i a × (H → Binary)) :=
      LinearMap.finrank_le_finrank_of_injective (coordinateMap_injective P a)
    _ = ∑ i : Fin 2, (Module.finrank Binary (projected P i a) + Fintype.card H) := by
      simp [Module.finrank_pi_fintype, Module.finrank_prod]
    _ ≤ ∑ _i : Fin 2, (P.rank + Fintype.card H) :=
      Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (hprimal i) _)
    _ = 2 * P.rank + 2 * Fintype.card H := by simp; omega

end Lax342547Proofs.TableSpaces
