import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
---
title: Compatibility and codimension of forward/reverse matrix restrictions
type: lemma
---
The overlap calculation in Lemma 5.5: prescribing ZᵀL and LW imposes
exactly the common ZᵀLW block of compatibility conditions when Z and W
have independent columns. This statement includes zero column ranks.
-/

namespace Lax342547.MixerCompatibility

variable {K I E F : Type} [Field K] [Fintype I] [Fintype E] [Fintype F]

def restrictions (Z : Matrix I E K) (W : Matrix I F K) :
    Matrix I I K →ₗ[K] Matrix E I K × Matrix I F K where
  toFun L := (Z.transpose * L, L * W)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c L := by simp [Matrix.mul_smul, Matrix.smul_mul]

def compatibility (Z : Matrix I E K) (W : Matrix I F K) :
    (Matrix E I K × Matrix I F K) →ₗ[K] Matrix E F K where
  toFun p := p.1 * W - Z.transpose * p.2
  map_add' x y := by simp [Matrix.add_mul, Matrix.mul_add, add_sub_add_comm]
  map_smul' c x := by simp [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

axiom compatible_extensions (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec)
    (A : Matrix E I K) (B : Matrix I F K) :
    (∃ L : Matrix I I K, Z.transpose * L = A ∧ L * W = B) ↔ A * W = Z.transpose * B

axiom restrictions_codimension (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) :
    Module.finrank K (LinearMap.range (restrictions Z W)) + Fintype.card E * Fintype.card F =
      Fintype.card E * Fintype.card I + Fintype.card I * Fintype.card F

end Lax342547.MixerCompatibility
