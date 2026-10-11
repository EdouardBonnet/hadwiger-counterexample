import Lax342547.DerivativeResponses

/-!
---
title: Full response obstructions are effective profiles plus selected atoms
type: lemma
---
The actual two derivative tests force both residual contractions to zero.
Double annihilation gives row and column membership in pin-plus-key spaces.
Unselected sparse support removes the keys. Linear retractions identify
the remaining row/column constraints with tensor-space membership, giving
the actual effective remainder after selected subtraction.
-/

namespace Lax342547.EffectiveObstructions

open Lax342547.MomentSpace Lax342547.ProjectedPins Lax342547.PrimalContractions
open Lax342547.TensorAnnihilators
open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.ExactPins Lax342547.PinLabelExclusions
open Lax342547.SparsePins Lax342547.BarredSpaces Lax342547.ResidualLabels
open Lax342547.TableSpaces Lax342547.TableContractions Lax342547.DerivativeResponses

axiom rows_of_contraction_zero {B : Type} [Fintype B]
    (M : Matrix B B Binary) (T : Submodule Binary (B → Binary))
    (h : ∀ ψ : Module.Dual Binary (B → Binary), T ≤ LinearMap.ker ψ →
      M.mulVecLin (coordinates ψ) = 0) : ∀ i, (fun j => M i j) ∈ T

axiom tensor_of_columns_rows {B : Type} [Fintype B]
    (M : Matrix B B Binary) (S T : Submodule Binary (B → Binary))
    (hcol : ∀ j, (fun i => M i j) ∈ S) (hrow : ∀ i, (fun j => M i j) ∈ T) :
    M ∈ tensorSpace S T

axiom unselected_vector {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Component (Tag k) × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R) (v : (Fin b → Binary) → Option (Base k n) → Binary)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (hfresh : ∀ z t, (W.left i z t).label ∉ A i)
    (h : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) ∈
      projected P i a ⊔ individualKeys W i a.1) :
    (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) ∈ projected P i a

axiom sparse_columns {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (p : Label → Coord → Binary) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary) (j : Coord × Base) :
    ∃ v : Label → Base → Binary,
      (fun a => (∑ s ∈ L, Lax342547.TensorBlocks.block p s (Z s)) a j) =
        ∑ s ∈ L, labelTensor p s (v s)

axiom transpose_blocks {Label Coord Base : Type}
    (p : Label → Coord → Binary) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary) :
    (∑ s ∈ L, Lax342547.TensorBlocks.block p s (Z s)).transpose =
      ∑ s ∈ L, Lax342547.TensorBlocks.block p s ((Z s).transpose)

axiom unselected_tensor {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (e : Component (Tag k)) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (hfresh : ∀ z t, (W.left i z t).label ∉ A i)
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (M : Moment k n b degree) (hM : M = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (hcol : ∀ j, (fun a => M a j) ∈ projected P i (e, true) ⊔ individualKeys W i e)
    (hrow : ∀ a, (fun j => M a j) ∈ projected P i (e, false) ⊔ individualKeys W i e) :
    M ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false))

axiom effective_component {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (hU : ∀ j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (L : Finset (Fin b → Binary)) (hL : L.card ≤ R) (hdisjoint : Disjoint L (chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : (x i).val e = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s)) :
    (x i).val e ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false))

axiom obstruction_decomposition {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∃ c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary,
      ∀ i, ((x - Lax342547.SelectedRemoval.selectedPart W c) i) ∈
        effective (Profile k n b degree) P i

end Lax342547.EffectiveObstructions
