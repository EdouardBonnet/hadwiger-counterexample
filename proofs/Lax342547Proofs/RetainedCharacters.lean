import Lax342547.RetainedCharacters
import Lax342547Proofs.QuotientFactors
import Lax342547Proofs.CoefficientPhase
import Lax342547Proofs.FrozenRecords

namespace Lax342547Proofs.RetainedCharacters
open Lax342547.RetainedCharacters

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ConcreteGeometry
open Lax342547.CoefficientPhase Lax342547.PushforwardWalsh

/--
---
conclusion: Lax342547.RetainedCharacters.coefficient_pair_form
---
-/
theorem coefficient_pair_form {I N : Type} [Fintype I] [Fintype N]
    (C : Matrix I I Binary) (X Y : Matrix N I Binary) : by
      classical
      exact coefficientPair C X Y = matrixPair (LinearMap.BilinForm.toMatrix' (actualForm X Y)) C := by
  classical
  unfold actualForm
  rw [LinearMap.BilinForm.toMatrix'_toBilin']
  unfold coefficientPair matrixPair
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, matrixEntry, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax342547.RetainedCharacters.binary_self_add
---
-/
theorem binary_self_add (z : Binary) : z + z = 0 := by
  rcases Lax342547Proofs.Walsh.binary_cases z with rfl | rfl <;> decide

/--
---
conclusion: Lax342547.RetainedCharacters.disagreement_projection
---
-/
theorem disagreement_projection {I N : Type} [Fintype I] [Fintype N]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (p q : (I → Binary) →ₗ[Binary] (I → Binary))
    (hp : D.mkQ.comp p = D.mkQ) (hq : E.mkQ.comp q = E.mkQ)
    (X Y : Matrix N I Binary) (T : LinearMap.BilinForm Binary (I → Binary))
    (hD : ∀ v ∈ D, ∀ w, actualForm X Y v w = T v w)
    (hE : ∀ v w, w ∈ E → actualForm X Y v w = T v w) : by
      classical
      let Z := p.toMatrix' * C * q.toMatrix'.transpose
      exact coefficientPair C X Y + matrixPair (LinearMap.BilinForm.toMatrix' T) C =
        coefficientPair Z X Y + matrixPair (LinearMap.BilinForm.toMatrix' T) Z := by
  classical
  let Z := p.toMatrix' * C * q.toMatrix'.transpose
  have hz := Lax342547Proofs.ProjectedCoefficients.projection_preserves_quotient_pairing C D E p q hp hq
  have ha := Lax342547Proofs.FrozenCharacters.zero_quotient_frozen_agreement
    (C - Z) D E (actualForm X Y) T hz hD hE
  rw [map_sub, map_sub] at ha
  change coefficientPair C X Y + matrixPair (LinearMap.BilinForm.toMatrix' T) C =
    coefficientPair Z X Y + matrixPair (LinearMap.BilinForm.toMatrix' T) Z
  rw [coefficient_pair_form C, coefficient_pair_form Z]
  have h0 : (matrixPair (LinearMap.BilinForm.toMatrix' (actualForm X Y)) C -
      matrixPair (LinearMap.BilinForm.toMatrix' (actualForm X Y)) Z) -
      (matrixPair (LinearMap.BilinForm.toMatrix' T) C - matrixPair (LinearMap.BilinForm.toMatrix' T) Z) = 0 :=
    sub_eq_zero.mpr ha
  have hchar : ∀ z : Binary, -z = z := by
    intro z
    rcases Lax342547Proofs.Walsh.binary_cases z with rfl | rfl <;> decide
  simp only [sub_eq_add_neg, hchar] at h0
  apply sub_eq_zero.mp
  simp only [sub_eq_add_neg, hchar]
  convert h0 using 1
  abel

/--
---
conclusion: Lax342547.RetainedCharacters.sign_abs
---
-/
theorem sign_abs (z : Binary) : |sign z| = 1 := by
  rcases Lax342547Proofs.Walsh.binary_cases z with rfl | rfl <;> norm_num [sign]

/--
---
conclusion: Lax342547.RetainedCharacters.rank_zero_matrix
---
-/
theorem rank_zero_matrix {I J : Type} [Fintype I] [Fintype J]
    (C : Matrix I J Binary) (h : C.rank = 0) : C = 0 := by
  classical
  have hr : LinearMap.range C.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have hz : C.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  ext i j
  have hj := LinearMap.congr_fun hz (Pi.single j 1)
  simpa using congrFun hj i

/--
---
conclusion: Lax342547.RetainedCharacters.retained_character_dichotomy
---
-/
theorem retained_character_dichotomy {ΩA ΩB I N : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype I] [Fintype N]
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (X : ΩA → Matrix N I Binary) (Y : ΩB → Matrix N I Binary)
    (D E : Submodule Binary (I → Binary)) (T : LinearMap.BilinForm Binary (I → Binary))
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a = 1) (hβsum : ∑ b, β b = 1)
    (hD : ∀ a b v, v ∈ D → ∀ w, actualForm (X a) (Y b) v w = T v w)
    (hE : ∀ a b v w, w ∈ E → actualForm (X a) (Y b) v w = T v w)
    (hcapA : ∀ r (A : Matrix I (Fin r) Binary), Function.Injective (D.mkQ.comp A.mulVecLin) →
      ∀ x, push α (fun a => factorImage A (X a)) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(r * Fintype.card N)))
    (hcapB : ∀ r (B : Matrix I (Fin r) Binary), Function.Injective (E.mkQ.comp B.mulVecLin) →
      ∀ y, push β (fun b => factorImage B (Y b)) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(r * Fintype.card N)))
    (C : Matrix I I Binary) : by
      classical
      let mean := ∑ a, ∑ b, α a * β b *
        sign (coefficientPair C (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) C)
      exact mean = 1 ∨ |mean| ≤ (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N) := by
  classical
  obtain ⟨p, hp, hpk, hpid⟩ := Lax342547Proofs.ProjectedCoefficients.exists_quotient_projection D
  obtain ⟨q, hq, hqk, hqid⟩ := Lax342547Proofs.ProjectedCoefficients.exists_quotient_projection E
  let Z := p.toMatrix' * C * q.toMatrix'.transpose
  have hd (a : ΩA) (b : ΩB) :
      coefficientPair C (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) C =
        coefficientPair Z (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) Z :=
    disagreement_projection C D E p q hp hq (X a) (Y b) T
      (fun v hv w => hD a b v hv w) (hE a b)
  by_cases hz : Z = 0
  · left
    have hzero (a : ΩA) (b : ΩB) :
        sign (coefficientPair C (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) C) = 1 := by
      rw [hd a b, hz]
      simp [coefficientPair, Lax342547Proofs.Walsh.sign_zero]
    simp only [hzero, mul_one, ← Finset.mul_sum, hβsum, hαsum]
  · right
    obtain ⟨A, B, hAB, hA, hB⟩ :=
      Lax342547Proofs.QuotientFactors.quotient_independent_factors C D E p q hpk hqk hpid hqid
    have hc (a : ΩA) (b : ΩB) :
        sign (coefficientPair C (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) C) =
        sign (matrixPair (LinearMap.BilinForm.toMatrix' T) Z) *
          phase (factorImage A (X a)) (factorImage B (Y b)) := by
      have hf := Lax342547Proofs.CoefficientPhase.independent_factor_phase A B (X a) (Y b)
      rw [hAB] at hf
      rw [hd a b, hf, Lax342547Proofs.Walsh.sign_add]
      change phase _ _ * _ = _ * phase _ _
      ring
    have h := Lax342547Proofs.GramTests.paper_image_walsh α β
      (fun a => factorImage A (X a)) (fun b => factorImage B (Y b))
      (fun _ => sign (matrixPair (LinearMap.BilinForm.toMatrix' T) Z)) (fun _ => 1)
      hα hβ hαsum.le hβsum.le
      (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hcapA Z.rank A hA)
      (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hcapB Z.rank B hB)
      (fun _ => (sign_abs _).le) (fun _ => by norm_num)
    have he : (∑ a, ∑ b, α a * β b *
        sign (coefficientPair C (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) C)) =
        ∑ a, ∑ b, α a * β b * sign (matrixPair (LinearMap.BilinForm.toMatrix' T) Z) * 1 *
          phase (factorImage A (X a)) (factorImage B (Y b)) := by
      simp only [hc, mul_one, mul_assoc]
    rw [← he] at h
    apply h.trans
    have hr : 1 ≤ Z.rank := Nat.one_le_iff_ne_zero.mpr (fun h => hz (rank_zero_matrix Z h))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have hdim : (Fintype.card N : ℝ) ≤ Z.rank * Fintype.card N := by
      exact_mod_cast Nat.le_mul_of_pos_left (Fintype.card N) hr
    nlinarith

end Lax342547Proofs.RetainedCharacters
