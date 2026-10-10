import Lax342547.TableSpaces
import Lax342547.BaselineRank

/-!
---
title: Primal blocks of the nominal spaces and their bounded table part
type: definition and theorem
---
The combined primal space has zero channel coordinates. Its intersection
with a table space has dimension at most twice the total pin rank, while
the table together with the primal space spans every nominal coordinate.
A family of at most twenty-eight key directions costs at most twenty-eight
more dimensions, independently of the ambient channel dimension.
-/

namespace Lax342547.NominalPrimal

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

def primal : Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i h, v (i, Sum.inr h) = 0}
  zero_mem' := by intro i h; rfl
  add_mem' := by intro v w hv hw i h; change v (i, Sum.inr h) + w (i, Sum.inr h) = 0; rw [hv, hw, add_zero]
  smul_mem' := by intro c v hv i h; change c * v (i, Sum.inr h) = 0; rw [hv, mul_zero]

def keySpace {I : Type} (endpoint : I → Fin 2) (ray : I → B → Binary) :
    Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) :=
  Submodule.span Binary (Set.range (fun x => primalEmbedding (endpoint x) (ray x)))

axiom table_spans (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    tableSpace P a ⊔ primal = ⊤

axiom table_primal_dimension [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Module.finrank Binary ↥(tableSpace P a ⊓ primal) ≤ 2 * P.rank

axiom key_space_bound {I : Type} [Fintype I] [Fintype B] [Fintype H]
    (endpoint : I → Fin 2) (ray : I → B → Binary) :
    keySpace (H := H) endpoint ray ≤ primal ∧
      Module.finrank Binary (keySpace (H := H) endpoint ray) ≤ Fintype.card I

end Lax342547.NominalPrimal
