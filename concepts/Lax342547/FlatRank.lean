import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
---
title: Stabilized ranks and the radical quotient
type: definition and theorem
---
The flat-level and quotient steps of Lemma 5.2. These statements apply to
arbitrary finite-dimensional symmetric bilinear forms; no positivity is used.
-/

namespace Lax342547.FlatRank

axiom exists_flat_level (r : ℕ → ℕ) (A R J : ℕ) (hmono : Monotone r)
    (hbound : ∀ j ≤ J, r j ≤ R) (hroom : A + 2 * R + 2 ≤ J) :
    ∃ j, A ≤ j ∧ j + 2 ≤ J ∧ r j = r (j + 1) ∧ r (j + 1) = r (j + 2)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

noncomputable def quotientPairing (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    LinearMap.BilinForm K (V ⧸ B.ker) :=
  LinearMap.IsRefl.liftQ₂ B B.ker hB.isRefl le_rfl

axiom quotientPairing_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (quotientPairing B hB).Nondegenerate

axiom quotient_restriction_surjective [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B)) :
    Function.Surjective (B.ker.mkQ.comp U.subtype)

axiom exists_commuting_idempotents [FiniteDimensional K V] {ι : Type}
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B))
    (shift : ι → U →ₗ[K] V)
    (hadj : ∀ a (x y : U), B (shift a x) y = B x (shift a y))
    (hidem : ∀ a (x y : U), B (shift a x) (shift a y) = B (shift a x) y)
    (hcomm : ∀ a c (x y : U), B (shift a x) (shift c y) = B (shift c x) (shift a y)) :
    ∃ M : ι → Module.End K (V ⧸ B.ker),
      (∀ a (x : U), M a (B.ker.mkQ x) = B.ker.mkQ (shift a x)) ∧
      (∀ a x y, quotientPairing B hB (M a x) y = quotientPairing B hB x (M a y)) ∧
      (∀ a, M a * M a = M a) ∧ ∀ a c, M a * M c = M c * M a

end Lax342547.FlatRank
