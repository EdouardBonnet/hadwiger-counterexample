import Lax342547.SmallTables
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.SetTheory.Cardinal.Finite

/-!
---
title: Bounded table data and linear-size nominal coefficient records
type: definition and theorem
---
For fixed pin and channel budgets, the number of small tables is bounded
independently of the primal dimension. Nominal pin bases can be padded to
a fixed number of coefficient vectors; their bit count grows linearly in
the primal dimension.
-/

namespace Lax342547.TableCounts

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces Lax342547.SmallTables

abbrev CoefficientCode (Comp B H : Type) (K : ℕ) :=
  (Comp × Bool) → Fin K → (Fin 2 × (B ⊕ H)) → Binary

axiom table_count {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (K : ℕ)
    (hP : P.rank ≤ K) (hQ : Q.rank ≤ K) :
    Nat.card (Table P Q) ≤ 2 ^ (2 * Fintype.card Comp * (2 * K + 2 * Fintype.card H) ^ 2)

axiom coefficient_code {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (K : ℕ) (hP : P.rank ≤ K) :
    ∃ code : CoefficientCode Comp B H K,
      ∀ a, Submodule.span Binary (Set.range (code a)) = P.space a

axiom coefficient_count {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H] (K : ℕ) :
    Nat.card (CoefficientCode Comp B H K) =
      2 ^ (4 * Fintype.card Comp * K * (Fintype.card B + Fintype.card H))

end Lax342547.TableCounts
