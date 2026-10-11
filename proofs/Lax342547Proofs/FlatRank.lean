import Lax342547.FlatRank
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.FlatRank

open Lax342547.FlatRank

/--
---
conclusion: Lax342547.FlatRank.exists_flat_level
---
Without two consecutive equal increments, each disjoint pair of steps
increases the rank. There are R+1 such pairs and only R possible increases.
-/
theorem exists_flat_level (r : ℕ → ℕ) (A R J : ℕ) (hmono : Monotone r)
    (hbound : ∀ j ≤ J, r j ≤ R) (hroom : A + 2 * R + 2 ≤ J) :
    ∃ j, A ≤ j ∧ j + 2 ≤ J ∧ r j = r (j + 1) ∧ r (j + 1) = r (j + 2) := by
  by_contra h
  have hgrowth : ∀ n, n ≤ R + 1 → n ≤ r (A + 2 * n) := by
    intro n
    induction n with
    | zero => exact fun _ => Nat.zero_le _
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have h₀ := hmono (show A + 2 * n ≤ A + 2 * n + 1 by omega)
      have h₁ := hmono (show A + 2 * n + 1 ≤ A + 2 * n + 2 by omega)
      have hne : r (A + 2 * n) ≠ r (A + 2 * n + 2) := by
        intro he
        apply h
        refine ⟨A + 2 * n, by omega, by omega, ?_, ?_⟩ <;> omega
      have hindex : A + 2 * (n + 1) = A + 2 * n + 2 := by omega
      rw [hindex]
      omega
  have hg := hgrowth (R + 1) le_rfl
  have hb := hbound (A + 2 * (R + 1)) (by omega)
  omega

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem quotientPairing_mk (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (x y : V) :
    quotientPairing B hB (B.ker.mkQ x) (B.ker.mkQ y) = B x y := rfl

theorem quotientPairing_symm (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (quotientPairing B hB).IsSymm := by
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := B.ker.mkQ_surjective x
  obtain ⟨y, rfl⟩ := B.ker.mkQ_surjective y
  exact hB.eq x y

/--
---
conclusion: Lax342547.FlatRank.quotientPairing_nondegenerate
---
Symmetry makes the left and right radicals equal. A class orthogonal to
every class has a representative in the radical, so it is zero.
-/
theorem quotientPairing_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (quotientPairing B hB).Nondegenerate := by
  have hleft : (quotientPairing B hB).SeparatingLeft := by
    intro x hx
    obtain ⟨x, rfl⟩ := B.ker.mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero B.ker).mpr
    change B x = 0
    ext y
    exact hx (B.ker.mkQ y)
  exact ⟨hleft, fun y hy => hleft y (fun x => (quotientPairing_symm B hB).eq y x |>.trans (hy x))⟩

theorem quotient_finrank (B : LinearMap.BilinForm K V) :
    Module.finrank K (V ⧸ B.ker) = Module.finrank K (LinearMap.range B) :=
  B.quotKerEquivRange.finrank_eq

variable [FiniteDimensional K V]

/--
---
conclusion: Lax342547.FlatRank.quotient_restriction_surjective
---
The restricted pairing factors through the image of the subspace in the
radical quotient. Equality of ranks forces that image to fill the quotient.
-/
theorem quotient_restriction_surjective (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B)) :
    Function.Surjective (B.ker.mkQ.comp U.subtype) := by
  let q := B.ker.mkQ.comp U.subtype
  let g := (quotientPairing B hB).compl₂ q
  have hfactor : B.restrict U = g.comp q := by ext x y; rfl
  have hd : Module.finrank K (V ⧸ B.ker) ≤ Module.finrank K (LinearMap.range q) := by
    rw [quotient_finrank B, ← hflat, hfactor, LinearMap.range_comp]
    exact Submodule.finrank_map_le g (LinearMap.range q)
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
    ((Submodule.finrank_le (LinearMap.range q)).antisymm hd))

theorem radical_restrict_of_flat (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B)) (x : U)
    (hx : ∀ y : U, B x y = 0) : ∀ y : V, B x y = 0 := by
  intro y
  obtain ⟨z, hz⟩ := Lax342547.FlatRank.quotient_restriction_surjective B hB U hflat (B.ker.mkQ y)
  change B.ker.mkQ (z : V) = B.ker.mkQ y at hz
  calc
    B x y = quotientPairing B hB (B.ker.mkQ x) (B.ker.mkQ y) := rfl
    _ = quotientPairing B hB (B.ker.mkQ x) (B.ker.mkQ z) := by rw [hz]
    _ = 0 := hx z

theorem exists_descended_shift (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B))
    (shift : U →ₗ[K] V) (hadj : ∀ x y : U, B (shift x) y = B x (shift y)) :
    ∃ M : (V ⧸ B.ker) →ₗ[K] (V ⧸ B.ker),
      ∀ x : U, M (B.ker.mkQ x) = B.ker.mkQ (shift x) := by
  let q := B.ker.mkQ.comp U.subtype
  have hsurj : Function.Surjective q := Lax342547.FlatRank.quotient_restriction_surjective B hB U hflat
  have hker : q.ker ≤ (B.ker.mkQ.comp shift).ker := by
    intro x hx
    change B.ker.mkQ (shift x) = 0
    apply (Lax342547.FlatRank.quotientPairing_nondegenerate B hB).1
    intro y
    obtain ⟨z, rfl⟩ := hsurj y
    change B (shift x) z = 0
    rw [hadj x z]
    have hx' : B (x : V) = 0 := (Submodule.Quotient.mk_eq_zero B.ker).mp hx
    exact LinearMap.congr_fun hx' (shift z)
  let M := (q.ker.liftQ (B.ker.mkQ.comp shift) hker).comp
    (q.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  refine ⟨M, ?_⟩
  intro x
  change q.ker.liftQ (B.ker.mkQ.comp shift) hker
    ((q.quotKerEquivOfSurjective hsurj).symm (q x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

omit [FiniteDimensional K V] in
theorem pairing_ext (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    {x y : V} (h : ∀ z, B x z = B y z) : x = y := by
  apply sub_eq_zero.mp
  apply hB.1
  intro z
  rw [map_sub, LinearMap.sub_apply, h z, sub_self]

/--
---
conclusion: Lax342547.FlatRank.exists_commuting_idempotents
---
Flatness makes the low-degree representatives surject onto the radical
quotient. Transfer the selector shifts through this surjection. Their
pairing identities prove well-definedness, self-adjointness, idempotence,
and commutativity using nondegeneracy of the quotient pairing.
-/
theorem exists_commuting_idempotents {ι : Type}
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
      (∀ a, M a * M a = M a) ∧ ∀ a c, M a * M c = M c * M a := by
  choose M hM using fun a => exists_descended_shift B hB U hflat (shift a) (hadj a)
  have hsurj := Lax342547.FlatRank.quotient_restriction_surjective B hB U hflat
  have hsym a x y : quotientPairing B hB (M a x) y = quotientPairing B hB x (M a y) := by
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    change quotientPairing B hB (M a (B.ker.mkQ x)) (B.ker.mkQ y) =
      quotientPairing B hB (B.ker.mkQ x) (M a (B.ker.mkQ y))
    rw [hM, hM]
    exact hadj a x y
  refine ⟨M, hM, hsym, ?_, ?_⟩
  · intro a
    apply LinearMap.ext
    intro x
    apply pairing_ext _ (Lax342547.FlatRank.quotientPairing_nondegenerate B hB)
    intro y
    change quotientPairing B hB (M a (M a x)) y = quotientPairing B hB (M a x) y
    rw [hsym]
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    change quotientPairing B hB (M a (B.ker.mkQ x)) (M a (B.ker.mkQ y)) =
      quotientPairing B hB (M a (B.ker.mkQ x)) (B.ker.mkQ y)
    rw [hM, hM]
    exact hidem a x y
  · intro a c
    apply LinearMap.ext
    intro x
    apply pairing_ext _ (Lax342547.FlatRank.quotientPairing_nondegenerate B hB)
    intro y
    change quotientPairing B hB (M a (M c x)) y = quotientPairing B hB (M c (M a x)) y
    rw [hsym a (M c x) y, hsym c (M a x) y]
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    change quotientPairing B hB (M c (B.ker.mkQ x)) (M a (B.ker.mkQ y)) =
      quotientPairing B hB (M a (B.ker.mkQ x)) (M c (B.ker.mkQ y))
    rw [hM, hM, hM, hM]
    exact hcomm c a x y

end Lax342547Proofs.FlatRank
