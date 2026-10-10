import Lax342547.ResponseMatrices
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
---
title: Compression preserving allowed point moments and the actual cut domain
type: definition and theorem
---
A projection can fix a prescribed vector space and preserve observations,
with rank bounded by the fixed-space dimension plus the observation rank.
Blockwise base maps fix the constant coordinate and selector factor, send
allowed points to allowed points, and preserve the actual cut-profile
space. Their ranks and the transformation of target matrices are checked.
The choice fixing every pin and residual target is treated separately.
-/

namespace Lax342547.BaseCompression

open Lax342547.MomentSpace
open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

axiom fixing_observed_projection {V X : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary V]
    (U : Submodule Binary V) (L : V →ₗ[Binary] X) :
    ∃ p : V →ₗ[Binary] V, (∀ v ∈ U, p v = v) ∧ L.comp p = L ∧
      Module.finrank Binary (LinearMap.range p) ≤
        Module.finrank Binary U + Module.finrank Binary (LinearMap.range L)

def liftBase {Coord Base : Type}
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary)) :
    (Coord × Option Base → Binary) →ₗ[Binary] (Coord × Option Base → Binary) where
  toFun v c := match c.2 with
    | none => v (c.1, none)
    | some b => f (fun b => v (c.1, some b)) b
  map_add' v w := by
    ext ⟨a, c⟩
    cases c with
    | none => rfl
    | some b => exact congrFun (f.map_add _ _) b
  map_smul' c v := by
    ext ⟨a, q⟩
    cases q with
    | none => rfl
    | some b => exact congrFun (f.map_smul c _) b

axiom liftBase_point {Label Coord Base : Type}
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary))
    (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    liftBase (Coord := Coord) f (point p s z) = point p s (f z)

noncomputable def tensorMap {B : Type} [Fintype B] (f : (B → Binary) →ₗ[Binary] (B → Binary)) :
    Matrix B B Binary →ₗ[Binary] Matrix B B Binary := by
  classical
  exact (mulRightLinearMap B Binary (LinearMap.toMatrix' f).transpose).comp
    (mulLeftLinearMap B Binary (LinearMap.toMatrix' f))

axiom tensorMap_point {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary))
    (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    tensorMap (liftBase f) (pointMoment p s z) = pointMoment p s (f z)

axiom tensorMap_moments {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary)) (p : Label → Coord → Binary)
    (A : Set Base)
    (hA : ∀ z, (∀ b, b ∉ A → z b = 0) → ∀ b, b ∉ A → f z b = 0) :
    (momentSpace p A).map (tensorMap (liftBase f)) ≤ momentSpace p A

abbrev Block (k : ℕ) := (Tag k × Tag k) ⊕ Fin 3

def blockMap {k n : ℕ} (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) :
    (Base k n → Binary) →ₗ[Binary] (Base k n → Binary) where
  toFun z q := match q with
    | Sum.inl ((d, t), i) => A (Sum.inl (d, t)) (fun j => z (Sum.inl ((d, t), j))) i
    | Sum.inr (q, i) => A (Sum.inr q) (fun j => z (Sum.inr (q, j))) i
  map_add' z w := by
    ext q
    rcases q with ⟨⟨d, t⟩, i⟩ | ⟨q, i⟩ <;> exact congrFun (LinearMap.map_add _ _ _) i
  map_smul' c z := by
    ext q
    rcases q with ⟨⟨d, t⟩, i⟩ | ⟨q, i⟩ <;> exact congrFun (LinearMap.map_smul _ c _) i

axiom blockMap_allowed {k n : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) (l : Tag k)
    (z : Base k n → Binary) (hz : ∀ q, q ∉ allowedBase k n l → z q = 0) :
    ∀ q, q ∉ allowedBase k n l → blockMap A z q = 0

axiom blockMap_tagSpace {k n b degree : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) (l : Tag k) :
    (tagSpace k n b degree l).map (tensorMap (liftBase (blockMap A))) ≤ tagSpace k n b degree l

def componentMap {Tag V : Type} [AddCommGroup V] [Module Binary V]
    (f : V →ₗ[Binary] V) : (Component Tag → V) →ₗ[Binary] (Component Tag → V) where
  toFun x e := f (x e)
  map_add' x y := by ext e; exact f.map_add _ _
  map_smul' c x := by ext e; exact f.map_smul c _

axiom componentMap_cut {Tag V : Type} [AddCommGroup V] [Module Binary V]
    (f : V →ₗ[Binary] V) (w : Tag → V) :
    componentMap (Tag := Tag) f (cutMap w) = cutMap (fun t => f (w t))

axiom blockMap_profile {k n b degree : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) :
    (Profile k n b degree).map (componentMap (tensorMap (liftBase (blockMap A)))) ≤
      Profile k n b degree

axiom liftBase_rank {Coord Base : Type} [Fintype Coord] [Fintype Base]
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary)) :
    Module.finrank Binary (LinearMap.range (liftBase (Coord := Coord) f)) ≤
      Fintype.card Coord * (1 + Module.finrank Binary (LinearMap.range f))

axiom matrixPair_trace {B : Type} [Fintype B] (M W : Matrix B B Binary) :
    Lax342547.ConcreteGeometry.matrixPair M W = Matrix.trace (M.transpose * W)

axiom matrixPair_tensorMap {B : Type} [Fintype B]
    (f : (B → Binary) →ₗ[Binary] (B → Binary)) (M W : Matrix B B Binary) : by
      classical
      exact Lax342547.ConcreteGeometry.matrixPair M (tensorMap f W) =
        Lax342547.ConcreteGeometry.matrixPair
          ((LinearMap.toMatrix' f).transpose * M * LinearMap.toMatrix' f) W

axiom tensorMap_target {B : Type} [Fintype B]
    (f : (B → Binary) →ₗ[Binary] (B → Binary)) (M : Matrix B B Binary)
    (hM : by classical exact (LinearMap.toMatrix' f).transpose * M * LinearMap.toMatrix' f = M) :
    (Lax342547.ConcreteGeometry.matrixPair M).comp (tensorMap f) =
      Lax342547.ConcreteGeometry.matrixPair M

axiom blockMap_rank {k n : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) :
    Module.finrank Binary (LinearMap.range (blockMap A)) ≤
      ∑ q, Module.finrank Binary (LinearMap.range (A q))

axiom concrete_compression_rank {k n b degree D : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary))
    (hA : ∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤ D) :
    Module.finrank Binary (LinearMap.range
      (liftBase (Coord := SelectorCoordinates b degree) (blockMap A))) ≤
      Fintype.card (SelectorCoordinates b degree) * (1 + ((2 * k + 1)^2 + 3) * D)

end Lax342547.BaseCompression
