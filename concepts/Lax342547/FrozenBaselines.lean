import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.BilinearMap

/-!
---
title: Baseline bilinear extensions retaining all frozen rows and columns
type: lemma
---
Split each table space into its stored pin part and a complement, retaining
the independent key space. An explicit bilinear formula extends both the
table and every actual row or column through a pin or key. No gradient
solvability or rank bound is assumed in this extension argument.
-/

namespace Lax342547.FrozenBaselines

open Lax342547.MomentSpace

variable {V W : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W]

structure Splitting (J D Keys : Submodule Binary V) where
  frozen : V →ₗ[Binary] V
  table : V →ₗ[Binary] J
  frozen_fixed : ∀ v ∈ D ⊔ Keys, frozen v = v
  table_zero : ∀ v ∈ D ⊔ Keys, table v = 0
  frozen_table : ∀ v : J, frozen v.val ∈ D
  table_sum : ∀ v : J, frozen v.val + (table v.val).val = v.val

def baseline {J D Keys : Submodule Binary V} {J' D' Keys' : Submodule Binary W}
    (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary) :
    V →ₗ[Binary] W →ₗ[Binary] Binary :=
  A.compl₁₂ S.frozen LinearMap.id + A.compl₁₂ LinearMap.id S'.frozen -
    A.compl₁₂ S.frozen S'.frozen + T.compl₁₂ S.table S'.table

def Compatible (J D : Submodule Binary V) (J' D' : Submodule Binary W)
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary) : Prop :=
  ∀ v : J, ∀ w : J', v.val ∈ D ∨ w.val ∈ D' → T v w = A v.val w.val

def ExtendsFrozen (D Keys : Submodule Binary V) (D' Keys' : Submodule Binary W)
    (A B : V →ₗ[Binary] W →ₗ[Binary] Binary) : Prop :=
  ∀ v w, v ∈ D ⊔ Keys ∨ w ∈ D' ⊔ Keys' → B v w = A v w

axiom splitting_exists (J D Keys : Submodule Binary V) (hD : D ≤ J) (hKeys : Disjoint J Keys) :
    Nonempty (Splitting J D Keys)

axiom baseline_properties (J D Keys : Submodule Binary V) (J' D' Keys' : Submodule Binary W)
    (hD : D ≤ J) (hD' : D' ≤ J')
    (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (h : Compatible J D J' D' A T) :
    ExtendsFrozen D Keys D' Keys' A (baseline S S' A T) ∧
      ∀ v : J, ∀ w : J', baseline S S' A T v.val w.val = T v w

end Lax342547.FrozenBaselines
