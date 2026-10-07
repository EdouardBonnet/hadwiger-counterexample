import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
---
title: The binary hole relation
type: definition
---
Fix binary vector spaces $X,V$, a functional $a:X\to\mathbb F_2$, and a
symmetric bilinear form $T$ on $X$. For each raw vertex $i$, let
$U_i:X\to V$ be injective and $u_i:V\to\mathbb F_2$ linear.

A hole between $i,j$ has witnesses $x,y\in X$ satisfying
$U_i x=U_j y$, $u_jU_i=a+T(x,\cdot)$,
$u_iU_j=a+T(y,\cdot)$, and $a(x)+a(y)=1$.
These are the equations of Definition 2.1.
-/

namespace Lax342547.HoleRelation

universe u v w

structure HoleData (Ω : Type u) (X : Type v) (V : Type w)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup V] [Module (ZMod 2) V] where
  a : X →ₗ[ZMod 2] ZMod 2
  T : LinearMap.BilinForm (ZMod 2) X
  symmetric : ∀ x y, T x y = T y x
  U : Ω → X →ₗ[ZMod 2] V
  injective : ∀ i, Function.Injective (U i)
  u : Ω → V →ₗ[ZMod 2] ZMod 2

variable {Ω : Type u} {X : Type v} {V : Type w}
variable [AddCommGroup X] [Module (ZMod 2) X]
variable [AddCommGroup V] [Module (ZMod 2) V]

def Hole (D : HoleData Ω X V) (i j : Ω) : Prop :=
  ∃ x y : X, D.U i x = D.U j y ∧
    (∀ z, D.u j (D.U i z) = D.a z + D.T x z) ∧
    (∀ z, D.u i (D.U j z) = D.a z + D.T y z) ∧
    D.a x + D.a y = 1

end Lax342547.HoleRelation
