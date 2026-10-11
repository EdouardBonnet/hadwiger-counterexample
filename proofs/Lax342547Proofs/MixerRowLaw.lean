import Lax342547.MixerRowLaw
import Lax342547Proofs.MixerCompatibility
import Lax342547.FiniteLinearLaw
import Lax342547.MixerCompatibility

namespace Lax342547Proofs.MixerRowLaw

set_option backward.isDefEq.respectTransparency false

open Lax342547.MixerCompatibility Lax342547.MixerRowLaw

variable {K I E F N : Type} [Field K] [Fintype I] [Fintype N]

theorem directions_surjective (D : Matrix I N K) (hD : Function.Injective D.mulVec) :
    Function.Surjective (directions (E := E) (F := F) D) := by
  classical
  obtain ⟨U, hU⟩ := MixerCompatibility.exists_left_inverse D hD
  have hDU : D.transpose * U.transpose = 1 := by simpa using congrArg Matrix.transpose hU
  rintro ⟨A, B⟩
  refine ⟨(A * U, U.transpose * B), ?_⟩
  apply Prod.ext
  · change A * U * D = A
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  · change D.transpose * (U.transpose * B) = B
    rw [← Matrix.mul_assoc, hDU, Matrix.one_mul]

theorem observations_codimension [Fintype E] [Fintype F]
    (Z : Matrix I E K) (W : Matrix I F K) (D : Matrix I N K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) (hD : Function.Injective D.mulVec) :
    Module.finrank K (Matrix E N K × Matrix N F K) ≤
      Module.finrank K (LinearMap.range (observations Z W D)) + Fintype.card E * Fintype.card F := by
  have h := Lax342547.FiniteLinearLaw.codimension_map_le (directions (E := E) (F := F) D)
    (directions_surjective D hD) (LinearMap.range (restrictions Z W))
  have hcompat := Lax342547.MixerCompatibility.restrictions_codimension Z W hZ hW
  have hdim : Module.finrank K (Matrix E I K × Matrix I F K) =
      Fintype.card E * Fintype.card I + Fintype.card I * Fintype.card F := by
    simp only [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, Nat.mul_one]
  rw [hdim, ← LinearMap.range_comp] at h
  change _ ≤ Module.finrank K (LinearMap.range ((directions D).comp (restrictions Z W))) + _
  omega

open Lax342547.MomentSpace
open scoped ENNReal

/--
---
conclusion: Lax342547.MixerRowLaw.row_law_bound
---
The full forward/reverse restrictions have exactly |E||F| compatibility
conditions. Reading only free directions is a surjective linear map on
the space of unconstrained lists, so it cannot increase codimension.
The binary uniform-image bound supplies the factor 2^(|E||F|).
-/
theorem row_law_bound {I E F N : Type} [Fintype I] [Fintype E] [Fintype F] [Fintype N]
    [DecidableEq I] [DecidableEq E] [DecidableEq F] [DecidableEq N]
    (Z : Matrix I E Binary) (W : Matrix I F Binary) (D : Matrix I N Binary)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) (hD : Function.Injective D.mulVec)
    (y : Matrix E N Binary × Matrix N F Binary) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (observations Z W D) y ≤
      2 ^ (Fintype.card E * Fintype.card F) * PMF.uniformOfFintype (Matrix E N Binary × Matrix N F Binary) y :=
  Lax342547.FiniteLinearLaw.uniform_image_bound _ _ (observations_codimension Z W D hZ hW hD) y

end Lax342547Proofs.MixerRowLaw
