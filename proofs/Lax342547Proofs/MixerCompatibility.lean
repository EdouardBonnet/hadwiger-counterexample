import Lax342547.MixerCompatibility
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Lax342547Proofs.MixerCompatibility

set_option backward.isDefEq.respectTransparency false

open Lax342547.MixerCompatibility

variable {K I E F : Type} [Field K] [Fintype I] [Fintype E] [Fintype F]

theorem exists_left_inverse [DecidableEq E] (Z : Matrix I E K) (hZ : Function.Injective Z.mulVec) :
    ∃ U : Matrix E I K, U * Z = 1 := by
  classical
  obtain ⟨f, hf⟩ := Z.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hZ)
  refine ⟨f.toMatrix', ?_⟩
  have he := congrArg LinearMap.toMatrix' hf
  have hZmat : Z.mulVecLin.toMatrix' = Z := by
    ext i j
    simp [LinearMap.toMatrix'_apply]
  simpa [LinearMap.toMatrix'_comp, hZmat] using he

theorem extension_of_left_inverses [DecidableEq E] [DecidableEq F]
    (Z : Matrix I E K) (W : Matrix I F K) (U : Matrix E I K) (V : Matrix F I K)
    (hU : U * Z = 1) (hV : V * W = 1) (A : Matrix E I K) (B : Matrix I F K)
    (hAB : A * W = Z.transpose * B) :
    ∃ L : Matrix I I K, Z.transpose * L = A ∧ L * W = B := by
  classical
  have hZU : Z.transpose * U.transpose = 1 := by simpa using congrArg Matrix.transpose hU
  refine ⟨U.transpose * A + B * V - U.transpose * (Z.transpose * B) * V, ?_, ?_⟩
  · simp [Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, hZU]
  · simp [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hV, hAB]

/--
---
conclusion: Lax342547.MixerCompatibility.compatible_extensions
---
Choose left inverses UZ=1 and VW=1. For compatible A,B the explicit
matrix UᵀA + BV - Uᵀ(ZᵀB)V has both prescribed restrictions. Necessity
is associativity of matrix multiplication.
-/
theorem compatible_extensions (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec)
    (A : Matrix E I K) (B : Matrix I F K) :
    (∃ L : Matrix I I K, Z.transpose * L = A ∧ L * W = B) ↔ A * W = Z.transpose * B := by
  classical
  constructor
  · rintro ⟨L, rfl, rfl⟩
    exact Matrix.mul_assoc _ _ _
  · intro hAB
    obtain ⟨U, hU⟩ := exists_left_inverse Z hZ
    obtain ⟨V, hV⟩ := exists_left_inverse W hW
    exact extension_of_left_inverses Z W U V hU hV A B hAB

theorem range_restrictions (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) :
    LinearMap.range (restrictions Z W) = LinearMap.ker (compatibility Z W) := by
  ext ⟨A, B⟩
  change (∃ L, (Z.transpose * L, L * W) = (A, B)) ↔ A * W - Z.transpose * B = 0
  simp only [Prod.mk.injEq, sub_eq_zero]
  exact compatible_extensions Z W hZ hW A B

omit [Fintype E] in
theorem compatibility_surjective (Z : Matrix I E K) (W : Matrix I F K)
    (hW : Function.Injective W.mulVec) : Function.Surjective (compatibility Z W) := by
  classical
  obtain ⟨V, hV⟩ := exists_left_inverse W hW
  intro C
  refine ⟨(C * V, 0), ?_⟩
  simp [compatibility, Matrix.mul_assoc, hV]

/--
---
conclusion: Lax342547.MixerCompatibility.restrictions_codimension
---
The image is exactly the kernel of the common-block compatibility map.
That map is onto the E-by-F matrices, so rank-nullity gives exactly
|E| |F| independent compatibility conditions.
-/
theorem restrictions_codimension (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) :
    Module.finrank K (LinearMap.range (restrictions Z W)) + Fintype.card E * Fintype.card F =
      Fintype.card E * Fintype.card I + Fintype.card I * Fintype.card F := by
  have h := (compatibility Z W).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (compatibility_surjective Z W hW),
    ← range_restrictions Z W hZ hW] at h
  simpa only [finrank_top, Module.finrank_prod, Module.finrank_matrix,
    Module.finrank_self, Nat.mul_one, Nat.add_comm] using h

end Lax342547Proofs.MixerCompatibility
