import Lax342547.NominalPrimal
import Lax342547.SmallTables

/-!
---
title: The 3K+28 baseline bound in the actual nominal coordinates
type: theorem
---
For the two stored pin spaces and independent primal key spaces, complete
one cross form while retaining all frozen entries and the whole table.
Both reciprocal primal-to-channel maps have rank at most 3K+28. The same
form satisfies both bounds, so no independent completions are silently
used for its two endpoint roles.
-/

namespace Lax342547.NominalBaselines

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces
open Lax342547.SmallTables Lax342547.NominalPrimal Lax342547.FrozenBaselines

axiom nominal_baseline {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a b : Comp × Bool)
    (Keys Keys' : Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary)) (K : ℕ)
    (hP : P.rank ≤ K) (hQ : Q.rank ≤ K)
    (hkey : Keys ≤ primal) (hkey' : Keys' ≤ primal)
    (hcard : Module.finrank Binary Keys ≤ 28) (hcard' : Module.finrank Binary Keys' ≤ 28)
    (hfresh : Disjoint (tableSpace P a) Keys) (hfresh' : Disjoint (tableSpace Q b) Keys')
    (A : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary]
      ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] Binary)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary)
    (h : Compatible (tableSpace P a) (P.space a) (tableSpace Q b) (Q.space b) A T) :
    ∃ F : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary]
        ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] Binary,
      ExtendsFrozen (P.space a) Keys (Q.space b) Keys' A F ∧
      (∀ v : tableSpace P a, ∀ w : tableSpace Q b, F v.val w.val = T v w) ∧
      ∀ z : Fin 2,
        Module.finrank Binary (LinearMap.range
          (F.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range
          (F.flip.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ 3 * K + 28

end Lax342547.NominalBaselines
