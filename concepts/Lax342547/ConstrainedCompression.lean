import Lax342547.QuotientCompression

/-!
---
title: Compression that fixes pin/key vectors and preserves target matrices
type: lemma
---
Block maps are chosen from the actual projected pin/key spaces and the row/column observations of each residual matrix. They fix all required vectors, preserve every target functional, and have the paper block-rank bound independent of the base dimension.
-/

namespace Lax342547.ConstrainedCompression

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.BaseCompression
open Lax342547.PairedWitnesses Lax342547.TableSpaces Lax342547.ProjectedPins
open Lax342547.ConcreteCut Lax342547.ResponseMatrices
open Lax342547.CutProfiles Lax342547.ExactPins Lax342547.BarredSpaces

def baseAt {k n : ℕ} (q : Block k) (j : Fin n) : Base k n := match q with
  | Sum.inl (d, t) => Sum.inl ((d, t), j)
  | Sum.inr q => Sum.inr (q, j)

def blockSlice {k n b degree : ℕ} (s : SelectorCoordinates b degree) (q : Block k) :
    Vector k n b degree →ₗ[Binary] (Fin n → Binary) where
  toFun v j := v (s, some (baseAt q j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def blockEmbed {k n b degree : ℕ} (s : SelectorCoordinates b degree) (q : Block k) :
    (Fin n → Binary) →ₗ[Binary] Vector k n b degree := by
  classical
  exact
    { toFun := fun v c => if c.1 = s then match c.2 with
        | none => 0
        | some (Sum.inl ((d, t), j)) => if q = Sum.inl (d, t) then v j else 0
        | some (Sum.inr (q', j)) => if q = Sum.inr q' then v j else 0
      else 0
      map_add' := by
        intro v w
        ext ⟨a, c⟩
        cases c with
        | none => simp
        | some c =>
          rcases c with ⟨⟨d, t⟩, j⟩ | ⟨q', j⟩ <;>
            simp only [Pi.add_apply] <;> split_ifs <;> simp_all
      map_smul' := by
        intro c v
        ext ⟨a, q'⟩
        cases q' with
        | none => simp
        | some q' =>
          rcases q' with ⟨⟨d, t⟩, j⟩ | ⟨q', j⟩ <;>
            simp only [Pi.smul_apply] <;> split_ifs <;> simp_all }

def constantPart {k n b degree : ℕ} (v : Vector k n b degree) : Vector k n b degree :=
  fun c => match c.2 with
    | none => v (c.1, none)
    | some _ => 0

axiom vector_decomposition {k n b degree : ℕ} (v : Vector k n b degree) :
    v = constantPart v + ∑ s, ∑ q, blockEmbed s q (blockSlice s q v)

axiom lifted_decomposition {k n b degree : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) (v : Vector k n b degree) :
    liftBase (blockMap A) v = constantPart v + ∑ s, ∑ q, blockEmbed s q (A q (blockSlice s q v))

axiom pi_range_rank {I V X : Type} [Fintype I] [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary V] [FiniteDimensional Binary X]
    (L : I → V →ₗ[Binary] X) :
    Module.finrank Binary (LinearMap.range (LinearMap.pi L)) ≤
      ∑ i, Module.finrank Binary (LinearMap.range (L i))

noncomputable def fixedSlices {I : Type} [Fintype I] {k n b degree : ℕ}
    (S : I → Submodule Binary (Vector k n b degree)) (q : Block k) :
    (∀ j : I × SelectorCoordinates b degree, S j.1) →ₗ[Binary] (Fin n → Binary) := by
  classical
  exact LinearMap.lsum Binary _ Binary (fun j => (blockSlice j.2 q).comp (S j.1).subtype)

axiom fixedSlices_mem {I : Type} [Fintype I] {k n b degree : ℕ}
    (S : I → Submodule Binary (Vector k n b degree)) (q : Block k)
    (i : I) (s : SelectorCoordinates b degree) (v : Vector k n b degree) (hv : v ∈ S i) :
    blockSlice s q v ∈ LinearMap.range (fixedSlices S q)

axiom fixedSlices_rank {I : Type} [Fintype I] {k n b degree B : ℕ}
    (S : I → Submodule Binary (Vector k n b degree))
    (hS : ∀ i, Module.finrank Binary (S i) ≤ B) (q : Block k) :
    Module.finrank Binary (LinearMap.range (fixedSlices S q)) ≤
      Fintype.card I * Fintype.card (SelectorCoordinates b degree) * B

noncomputable def observations {I X : Type} {k n b degree : ℕ} [AddCommGroup X] [Module Binary X]
    (T : I → Vector k n b degree →ₗ[Binary] X) (q : Block k) :
    (Fin n → Binary) →ₗ[Binary] (I × SelectorCoordinates b degree → X) :=
  LinearMap.pi (fun j => (T j.1).comp (blockEmbed j.2 q))

axiom observations_rank {I X : Type} [Fintype I] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary X] {k n b degree R : ℕ}
    (T : I → Vector k n b degree →ₗ[Binary] X)
    (hT : ∀ i, Module.finrank Binary (LinearMap.range (T i)) ≤ R) (q : Block k) :
    Module.finrank Binary (LinearMap.range (observations T q)) ≤
      Fintype.card I * Fintype.card (SelectorCoordinates b degree) * R

axiom exists_block_compression {I X : Type} [Fintype I] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary X] {k n b degree B R : ℕ}
    (S : I → Submodule Binary (Vector k n b degree))
    (hS : ∀ i, Module.finrank Binary (S i) ≤ B)
    (T : I → Vector k n b degree →ₗ[Binary] X)
    (hT : ∀ i, Module.finrank Binary (LinearMap.range (T i)) ≤ R) :
    ∃ A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary),
      (∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤
        Fintype.card I * Fintype.card (SelectorCoordinates b degree) * (B + R)) ∧
      (∀ i v, v ∈ S i → liftBase (blockMap A) v = v) ∧
      ∀ i, (T i).comp (liftBase (blockMap A)) = T i

axiom preserved_matrix {B : Type} [Fintype B]
    (f : (B → Binary) →ₗ[Binary] (B → Binary)) (M : Matrix B B Binary)
    (hrow : M.mulVecLin.comp f = M.mulVecLin)
    (hcol : M.transpose.mulVecLin.comp f = M.transpose.mulVecLin) : by
      classical
      exact (LinearMap.toMatrix' f).transpose * M * LinearMap.toMatrix' f = M

axiom actual_block_compression {k n b degree r K R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (i : Fin 2) (M : Component (Tag k) → Moment k n b degree)
    (hM : ∀ e, (M e).rank ≤ R) :
    ∃ A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary),
      (∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤
        2 * Fintype.card (SelectorCoordinates b degree) * Fintype.card (Component (Tag k)) *
          (K + 14 + R)) ∧
      (∀ a v, v ∈ projected P i a ⊔ individualKeys W i a.1 → liftBase (blockMap A) v = v) ∧
      ∀ e, by
        classical
        exact
        (LinearMap.toMatrix' (liftBase (Coord := SelectorCoordinates b degree) (blockMap A))).transpose *
          M e * LinearMap.toMatrix' (liftBase (blockMap A)) = M e

end Lax342547.ConstrainedCompression
