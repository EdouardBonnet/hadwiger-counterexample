import Lax342547Proofs.FlatRank
import Lax342547.FlatRank

namespace Lax342547Proofs.FlatMap

open Lax342547.FlatRank

variable {K U V : Type} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K U] [FiniteDimensional K V]

theorem quotient_map_surjective (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (f : U →ₗ[K] V)
    (hflat : Module.finrank K (LinearMap.range (B.comp f f)) =
      Module.finrank K (LinearMap.range B)) :
    Function.Surjective (B.ker.mkQ.comp f) := by
  let q := B.ker.mkQ.comp f
  let g := (quotientPairing B hB).compl₂ q
  have hfactor : B.comp f f = g.comp q := by ext x y; rfl
  have hd : Module.finrank K (V ⧸ B.ker) ≤ Module.finrank K (LinearMap.range q) := by
    rw [FlatRank.quotient_finrank B, ← hflat, hfactor, LinearMap.range_comp]
    exact Submodule.finrank_map_le g (LinearMap.range q)
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
    ((Submodule.finrank_le (LinearMap.range q)).antisymm hd))

theorem exists_descended_shift (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (f : U →ₗ[K] V)
    (hflat : Module.finrank K (LinearMap.range (B.comp f f)) =
      Module.finrank K (LinearMap.range B))
    (shift : U →ₗ[K] V) (hadj : ∀ x y, B (shift x) (f y) = B (f x) (shift y)) :
    ∃ M : (V ⧸ B.ker) →ₗ[K] (V ⧸ B.ker),
      ∀ x, M (B.ker.mkQ (f x)) = B.ker.mkQ (shift x) := by
  let q := B.ker.mkQ.comp f
  have hsurj : Function.Surjective q := quotient_map_surjective B hB f hflat
  have hker : q.ker ≤ (B.ker.mkQ.comp shift).ker := by
    intro x hx
    change B.ker.mkQ (shift x) = 0
    apply (Lax342547.FlatRank.quotientPairing_nondegenerate B hB).1
    intro y
    obtain ⟨z, rfl⟩ := hsurj y
    change B (shift x) (f z) = 0
    rw [hadj x z]
    have hx' : B (f x) = 0 := (Submodule.Quotient.mk_eq_zero B.ker).mp hx
    exact LinearMap.congr_fun hx' (shift z)
  let M := (q.ker.liftQ (B.ker.mkQ.comp shift) hker).comp
    (q.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  refine ⟨M, ?_⟩
  intro x
  change q.ker.liftQ (B.ker.mkQ.comp shift) hker
    ((q.quotKerEquivOfSurjective hsurj).symm (q x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

theorem exists_commuting_idempotents {ι : Type}
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (f : U →ₗ[K] V)
    (hflat : Module.finrank K (LinearMap.range (B.comp f f)) =
      Module.finrank K (LinearMap.range B))
    (shift : ι → U →ₗ[K] V)
    (hadj : ∀ a x y, B (shift a x) (f y) = B (f x) (shift a y))
    (hidem : ∀ a x y, B (shift a x) (shift a y) = B (shift a x) (f y))
    (hcomm : ∀ a c x y, B (shift a x) (shift c y) = B (shift c x) (shift a y)) :
    ∃ M : ι → Module.End K (V ⧸ B.ker),
      (∀ a x, M a (B.ker.mkQ (f x)) = B.ker.mkQ (shift a x)) ∧
      (∀ a x y, quotientPairing B hB (M a x) y = quotientPairing B hB x (M a y)) ∧
      (∀ a, M a * M a = M a) ∧ ∀ a c, M a * M c = M c * M a := by
  choose M hM using fun a => exists_descended_shift B hB f hflat (shift a) (hadj a)
  have hsurj := quotient_map_surjective B hB f hflat
  have hsym a x y : quotientPairing B hB (M a x) y = quotientPairing B hB x (M a y) := by
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    change quotientPairing B hB (M a (B.ker.mkQ (f x))) (B.ker.mkQ (f y)) =
      quotientPairing B hB (B.ker.mkQ (f x)) (M a (B.ker.mkQ (f y)))
    rw [hM, hM]
    exact hadj a x y
  refine ⟨M, hM, hsym, ?_, ?_⟩
  · intro a
    apply LinearMap.ext
    intro x
    apply FlatRank.pairing_ext _ (Lax342547.FlatRank.quotientPairing_nondegenerate B hB)
    intro y
    change quotientPairing B hB (M a (M a x)) y = quotientPairing B hB (M a x) y
    rw [hsym]
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    change quotientPairing B hB (M a (B.ker.mkQ (f x))) (M a (B.ker.mkQ (f y))) =
      quotientPairing B hB (M a (B.ker.mkQ (f x))) (B.ker.mkQ (f y))
    rw [hM, hM]
    exact hidem a x y
  · intro a c
    apply LinearMap.ext
    intro x
    apply FlatRank.pairing_ext _ (Lax342547.FlatRank.quotientPairing_nondegenerate B hB)
    intro y
    change quotientPairing B hB (M a (M c x)) y = quotientPairing B hB (M c (M a x)) y
    rw [hsym a (M c x) y, hsym c (M a x) y]
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    change quotientPairing B hB (M c (B.ker.mkQ (f x))) (M a (B.ker.mkQ (f y))) =
      quotientPairing B hB (M a (B.ker.mkQ (f x))) (M c (B.ker.mkQ (f y)))
    rw [hM, hM, hM, hM]
    exact hcomm c a x y

end Lax342547Proofs.FlatMap
