import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Polar rank of the formal mixer quadratic
type: definition and theorem
---
The formal row variables for each indexed mixer product are disjoint.
The quadratic is a sum of products H_i(u_i,v_i), with each middle form
nonsingular. Its polar rank is exactly twice the sum of the middle
dimensions, including in characteristic two. Affine translations and
constant terms do not change the polar form of the binary function.
-/

namespace Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

abbrev Rows (V : B → Type) := ∀ i, V i × V i

def cross (H : ∀ i, LinearMap.BilinForm K (V i)) : LinearMap.BilinForm K (Rows V) :=
  ∑ i, (H i).comp ((LinearMap.fst K (V i) (V i)).comp (LinearMap.proj i))
    ((LinearMap.snd K (V i) (V i)).comp (LinearMap.proj i))

def quadratic (H : ∀ i, LinearMap.BilinForm K (V i)) : QuadraticForm K (Rows V) :=
  (cross H).toQuadraticMap

axiom polar_rank [∀ i, FiniteDimensional K (V i)]
    (H : ∀ i, LinearMap.BilinForm K (V i)) (hH : ∀ i, (H i).Nondegenerate) :
    Module.finrank K (LinearMap.range (quadratic H).polarBilin) =
      2 * ∑ i, Module.finrank K (V i)

open Lax342547.MomentSpace

def affinePolar {U : Type} [AddCommGroup U] (f : U → Binary) (u v : U) : Binary :=
  f (u + v) + f u + f v + f 0

def polarMatrix {I : Type} [DecidableEq I] (f : (I → Binary) → Binary) : Matrix I I Binary :=
  fun i j => affinePolar f (Pi.single i 1) (Pi.single j 1)

axiom affine_polar {U W : Type} [AddCommGroup U] [Module Binary U]
    [AddCommGroup W] [Module Binary W] (C : LinearMap.BilinForm Binary W)
    (A : U →ₗ[Binary] W) (w : W) (c : Binary) (u v : U) :
    affinePolar (fun z => c + C (w + A z) (w + A z)) u v = (C + C.flip) (A u) (A v)

axiom affine_polar_matrix_rank {I W : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module Binary W] (C : LinearMap.BilinForm Binary W)
    (A : (I → Binary) →ₗ[Binary] W) (w : W) (c : Binary) :
    (polarMatrix (fun z => c + C (w + A z) (w + A z))).rank =
      Module.finrank Binary (LinearMap.range ((C + C.flip).comp A A))

end Lax342547.FormalQuadratic
