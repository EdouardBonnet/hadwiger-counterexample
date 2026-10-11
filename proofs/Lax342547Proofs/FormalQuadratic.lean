import Lax342547.FormalQuadratic
import Lax342547Proofs.GramRank
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.FormalQuadratic

set_option backward.isDefEq.respectTransparency false

open Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

theorem cross_apply (H : ∀ i, LinearMap.BilinForm K (V i)) (x y : Rows V) :
    cross H x y = ∑ i, H i (x i).1 (y i).2 := by
  simp [cross, LinearMap.sum_apply]

theorem quadratic_apply (H : ∀ i, LinearMap.BilinForm K (V i)) (x : Rows V) :
    quadratic H x = ∑ i, H i (x i).1 (x i).2 := cross_apply H x x

theorem polar_apply (H : ∀ i, LinearMap.BilinForm K (V i)) (x y : Rows V) :
    (quadratic H).polarBilin x y = ∑ i, (H i (x i).1 (y i).2 + H i (y i).1 (x i).2) := by
  rw [quadratic, LinearMap.BilinMap.polarBilin_toQuadraticMap]
  simp [cross_apply, Finset.sum_add_distrib]

theorem polar_apply_single [DecidableEq B] (H : ∀ i, LinearMap.BilinForm K (V i))
    (x : Rows V) (i : B) (y : V i × V i) :
    (quadratic H).polarBilin x (Pi.single i y) = H i (x i).1 y.2 + H i y.1 (x i).2 := by
  rw [polar_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem polar_injective (H : ∀ i, LinearMap.BilinForm K (V i))
    (hH : ∀ i, (H i).Nondegenerate) : Function.Injective (quadratic H).polarBilin := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  funext i
  apply Prod.ext
  · apply (hH i).1
    intro v
    have h := LinearMap.congr_fun hx (Pi.single i (0, v))
    simpa only [polar_apply_single, map_zero, LinearMap.zero_apply, zero_add, add_zero] using h
  · apply (hH i).2
    intro u
    have h := LinearMap.congr_fun hx (Pi.single i (u, 0))
    simpa only [polar_apply_single, map_zero, LinearMap.zero_apply, zero_add, add_zero] using h

/--
---
conclusion: Lax342547.FormalQuadratic.polar_rank
---
Test one half of one formal block at a time. Nonsingularity of the
middle form forces both coordinates of every radical vector to vanish.
Thus the polar map is injective and its rank is the full row dimension.
-/
theorem polar_rank [∀ i, FiniteDimensional K (V i)]
    (H : ∀ i, LinearMap.BilinForm K (V i)) (hH : ∀ i, (H i).Nondegenerate) :
    Module.finrank K (LinearMap.range (quadratic H).polarBilin) =
      2 * ∑ i, Module.finrank K (V i) := by
  rw [LinearMap.finrank_range_of_inj (polar_injective H hH)]
  simp [Rows, Module.finrank_pi_fintype, Module.finrank_prod, Finset.sum_add_distrib, two_mul]

open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.FormalQuadratic.affine_polar
---
Expand the four evaluations of the affine quadratic in the binary field.
The constant, linear, and translated quadratic terms occur twice and
cancel; only the symmetrized bilinear part on A(u), A(v) remains.
-/
theorem affine_polar {U W : Type} [AddCommGroup U] [Module Binary U]
    [AddCommGroup W] [Module Binary W] (C : LinearMap.BilinForm Binary W)
    (A : U →ₗ[Binary] W) (w : W) (c : Binary) (u v : U) :
    affinePolar (fun z => c + C (w + A z) (w + A z)) u v = (C + C.flip) (A u) (A v) := by
  simp only [affinePolar, map_add, map_zero, add_zero, LinearMap.add_apply]
  abel_nf
  simp [show (2 : Binary) = 0 by decide, show (4 : Binary) = 0 by decide, add_comm]

/--
---
conclusion: Lax342547.FormalQuadratic.affine_polar_matrix_rank
---
The binary polar matrix is the Gram matrix of the pulled-back
symmetrized form on the coordinate basis. That basis spans, so its
matrix rank equals the rank of the bilinear map.
-/
theorem affine_polar_matrix_rank {I W : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module Binary W] (C : LinearMap.BilinForm Binary W)
    (A : (I → Binary) →ₗ[Binary] W) (w : W) (c : Binary) :
    (polarMatrix (fun z => c + C (w + A z) (w + A z))).rank =
      Module.finrank Binary (LinearMap.range ((C + C.flip).comp A A)) := by
  let B : LinearMap.BilinForm Binary (I → Binary) := (C + C.flip).comp A A
  have hB : B.IsSymm := ⟨fun x y => by
    change C (A x) (A y) + C (A y) (A x) = C (A y) (A x) + C (A x) (A y)
    exact add_comm _ _⟩
  have heq : polarMatrix (fun z => c + C (w + A z) (w + A z)) =
      GramRank.gram B (Pi.basisFun Binary I) := by
    ext i j
    simpa only [polarMatrix, GramRank.gram, Pi.basisFun_apply, B, LinearMap.BilinForm.comp_apply] using
      Lax342547.FormalQuadratic.affine_polar C A w c (Pi.single i 1) (Pi.single j 1)
  rw [heq]
  exact GramRank.rank_gram_eq B hB _ (Pi.basisFun Binary I).span_eq

end Lax342547Proofs.FormalQuadratic
