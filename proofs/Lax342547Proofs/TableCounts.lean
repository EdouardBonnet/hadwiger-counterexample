import Lax342547.TableCounts
import Lax342547Proofs.FiniteLinearLaw
import Lax342547.TableSpaces

namespace Lax342547Proofs.TableCounts

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces Lax342547.SmallTables
open Lax342547.TableCounts

theorem bilinear_card {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] [Fintype V] [Fintype W]
    [FiniteDimensional Binary V] [FiniteDimensional Binary W] :
    Nat.card (V →ₗ[Binary] W →ₗ[Binary] Binary) =
      2 ^ (Module.finrank Binary V * Module.finrank Binary W) := by
  classical
  let : Finite (W →ₗ[Binary] Binary) :=
    Finite.of_injective (fun f : W →ₗ[Binary] Binary => (f : W → Binary)) DFunLike.coe_injective
  let : Finite (V →ₗ[Binary] W →ₗ[Binary] Binary) := Finite.of_injective
    (fun f : V →ₗ[Binary] W →ₗ[Binary] Binary => (f : V → W →ₗ[Binary] Binary))
    DFunLike.coe_injective
  let : Fintype (V →ₗ[Binary] W →ₗ[Binary] Binary) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, FiniteLinearLaw.binary_card,
    Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_self, mul_one]

/--
---
conclusion: Lax342547.TableCounts.table_count
---
Each bilinear form is determined by a matrix with one entry per pair of
basis vectors. Both table domains have dimension at most 2K+2h. Multiply
the binary matrix counts over both cross orientations and all components.
-/
theorem table_count {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (K : ℕ)
    (hP : P.rank ≤ K) (hQ : Q.rank ≤ K) :
    Nat.card (Table P Q) ≤ 2 ^ (2 * Fintype.card Comp * (2 * K + 2 * Fintype.card H) ^ 2) := by
  classical
  let equiv : Table P Q ≃
      (∀ e, tableSpace P (e, true) →ₗ[Binary] tableSpace Q (e, false) →ₗ[Binary] Binary) ×
      (∀ e, tableSpace Q (e, true) →ₗ[Binary] tableSpace P (e, false) →ₗ[Binary] Binary) :=
    { toFun := fun T => (T.forward, T.reverse)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_pi, Nat.card_pi]
  simp_rw [bilinear_card]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hdP (a : Comp × Bool) : Module.finrank Binary (tableSpace P a) ≤
      2 * K + 2 * Fintype.card H :=
    (Lax342547.TableSpaces.table_dimension P a).trans (by omega)
  have hdQ (a : Comp × Bool) : Module.finrank Binary (tableSpace Q a) ≤
      2 * K + 2 * Fintype.card H :=
    (Lax342547.TableSpaces.table_dimension Q a).trans (by omega)
  have hsum₁ : (∑ e, Module.finrank Binary (tableSpace P (e, true)) *
      Module.finrank Binary (tableSpace Q (e, false))) ≤
      Fintype.card Comp * (2 * K + 2 * Fintype.card H) ^ 2 := by
    calc
      _ ≤ ∑ _e : Comp, (2 * K + 2 * Fintype.card H) ^ 2 := by
        apply Finset.sum_le_sum
        intro e _
        simpa only [pow_two] using Nat.mul_le_mul (hdP (e, true)) (hdQ (e, false))
      _ = _ := by simp
  have hsum₂ : (∑ e, Module.finrank Binary (tableSpace Q (e, true)) *
      Module.finrank Binary (tableSpace P (e, false))) ≤
      Fintype.card Comp * (2 * K + 2 * Fintype.card H) ^ 2 := by
    calc
      _ ≤ ∑ _e : Comp, (2 * K + 2 * Fintype.card H) ^ 2 := by
        apply Finset.sum_le_sum
        intro e _
        simpa only [pow_two] using Nat.mul_le_mul (hdQ (e, true)) (hdP (e, false))
      _ = _ := by simp
  calc
    _ ≤ 2 * (Fintype.card Comp * (2 * K + 2 * Fintype.card H) ^ 2) := by omega
    _ = _ := by ring

theorem padded_basis {V : Type} [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary V] (S : Submodule Binary V) (K : ℕ)
    (hK : Module.finrank Binary S ≤ K) :
    ∃ v : Fin K → V, Submodule.span Binary (Set.range v) = S := by
  classical
  let b := Module.finBasis Binary S
  let v : Fin K → V := fun i => if hi : i.val < Module.finrank Binary S then (b ⟨i.val, hi⟩).val else 0
  refine ⟨v, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    dsimp [v]
    split
    · exact (b _).property
    · exact S.zero_mem
  · have hspan : Submodule.span Binary (Set.range (fun i => (b i).val)) = S := by
      change Submodule.span Binary (Set.range (S.subtype ∘ b)) = S
      rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [← hspan]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i.val, i.isLt.trans_le hK⟩, ?_⟩
    simp [v, i.isLt]

/--
---
conclusion: Lax342547.TableCounts.coefficient_code
---
Every component/sign pin space has dimension at most the total pin
budget. Pad one of its bases to K vectors, giving a uniform coefficient
array whose span recovers that precise nominal subspace.
-/
theorem coefficient_code {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (K : ℕ) (hP : P.rank ≤ K) :
    ∃ code : CoefficientCode Comp B H K,
      ∀ a, Submodule.span Binary (Set.range (code a)) = P.space a := by
  have hdim (a : Comp × Bool) : Module.finrank Binary (P.space a) ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans hP
  choose v hv using fun a => padded_basis (P.space a) K (hdim a)
  exact ⟨v, hv⟩

/--
---
conclusion: Lax342547.TableCounts.coefficient_count
---
The padded record has one bit per component, sign, basis index, endpoint,
and primal-or-channel coordinate. Count these independent binary slots.
-/
theorem coefficient_count {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H] (K : ℕ) :
    Nat.card (CoefficientCode Comp B H K) =
      2 ^ (4 * Fintype.card Comp * K * (Fintype.card B + Fintype.card H)) := by
  classical
  simp only [CoefficientCode, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, Binary, ZMod.card, ← pow_mul]
  congr 1
  ring

end Lax342547Proofs.TableCounts
