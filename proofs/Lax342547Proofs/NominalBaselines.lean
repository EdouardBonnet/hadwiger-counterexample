import Lax342547.NominalBaselines
import Lax342547.BaselineRank
import Lax342547.NominalPrimal
import Lax342547.TableSpaces

namespace Lax342547Proofs.NominalBaselines

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces
open Lax342547.SmallTables Lax342547.NominalPrimal Lax342547.FrozenBaselines

/--
---
conclusion: Lax342547.NominalBaselines.nominal_baseline
---
The combined primal portion of the table has dimension at most 2K,
the key span costs at most 28, and the opposite stored pin space at
most K. Apply the bilateral bounded baseline construction to the two
actual nominal table spaces, then evaluate on each endpoint's channels.
-/
theorem nominal_baseline {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
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
          (F.flip.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ 3 * K + 28 := by
  obtain ⟨F, hfrozen, htable, hleft, hright⟩ := Lax342547.BaselineRank.bounded_baseline
    (C := H → Binary)
    (tableSpace P a) (P.space a) Keys primal (tableSpace Q b) (Q.space b) Keys' primal
    (Lax342547.TableSpaces.pin_le_table P a) (Lax342547.TableSpaces.pin_le_table Q b) hfresh hfresh'
    (Lax342547.NominalPrimal.table_spans P a) hkey (Lax342547.NominalPrimal.table_spans Q b) hkey' A T h
  have hdP : Module.finrank Binary (P.space a) ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans hP
  have hdQ : Module.finrank Binary (Q.space b) ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans hQ
  have htP : Module.finrank Binary ↥(tableSpace P a ⊓ primal) ≤ 2 * K :=
    (Lax342547.NominalPrimal.table_primal_dimension P a).trans (Nat.mul_le_mul_left 2 hP)
  have htQ : Module.finrank Binary ↥(tableSpace Q b ⊓ primal) ≤ 2 * K :=
    (Lax342547.NominalPrimal.table_primal_dimension Q b).trans (Nat.mul_le_mul_left 2 hQ)
  refine ⟨F, hfrozen, htable, ?_⟩
  intro z
  constructor
  · exact (hleft (tableChannel Q b z)).trans (by omega)
  · exact (hright (tableChannel P a z)).trans (by omega)

end Lax342547Proofs.NominalBaselines
