import Lax342547.PushforwardWalsh
import Lax342547.Walsh

namespace Lax342547Proofs.PushforwardWalsh
open Lax342547.PushforwardWalsh

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh

/--
---
conclusion: Lax342547.PushforwardWalsh.push_nonneg
---
-/
theorem push_nonneg {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X)
    (hρ : ∀ ω, 0 ≤ ρ ω) (x : X) : 0 ≤ push ρ image x := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hρ ω
  · exact le_rfl

/--
---
conclusion: Lax342547.PushforwardWalsh.push_total
---
-/
theorem push_total {Ω X : Type} [Fintype Ω] [Fintype X] (ρ : Ω → ℝ) (image : Ω → X) :
    ∑ x, push ρ image x = ∑ ω, ρ ω := by
  classical
  unfold push
  rw [Finset.sum_comm]
  simp [eq_comm]

/--
---
conclusion: Lax342547.PushforwardWalsh.push_integral
---
-/
theorem push_integral {Ω X : Type} [Fintype Ω] [Fintype X]
    (ρ : Ω → ℝ) (image : Ω → X) (f : X → ℝ) :
    ∑ x, push ρ image x * f x = ∑ ω, ρ ω * f (image ω) := by
  classical
  unfold push
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul, eq_comm]

/--
---
conclusion: Lax342547.PushforwardWalsh.signed_push_bound
---
-/
theorem signed_push_bound {Ω X : Type} [Fintype Ω] (ρ w : Ω → ℝ) (image : Ω → X)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hw : ∀ ω, |w ω| ≤ 1) (x : X) :
    |push (fun ω => ρ ω * w ω) image x| ≤ push ρ image x := by
  classical
  unfold push
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro ω _
  split_ifs
  · rw [abs_mul, abs_of_nonneg (hρ ω)]
    simpa using mul_le_mul_of_nonneg_left (hw ω) (hρ ω)
  · simp

/--
---
conclusion: Lax342547.PushforwardWalsh.conditional_weight_bound
---
-/
theorem conditional_weight_bound {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hw : ∀ ω, |w ω| ≤ 1) (x : X) : |conditionalWeight ρ w image x| ≤ 1 := by
  have hb := Lax342547.PushforwardWalsh.signed_push_bound ρ w image hρ hw x
  have hn := Lax342547.PushforwardWalsh.push_nonneg ρ image hρ x
  unfold conditionalWeight
  by_cases h : push ρ image x = 0
  · simp [h]
  · rw [abs_div, abs_of_nonneg hn]
    exact (div_le_one (lt_of_le_of_ne hn (Ne.symm h))).mpr hb

/--
---
conclusion: Lax342547.PushforwardWalsh.conditional_weight_reconstruction
---
-/
theorem conditional_weight_reconstruction {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hw : ∀ ω, |w ω| ≤ 1) (x : X) :
    push ρ image x * conditionalWeight ρ w image x =
      push (fun ω => ρ ω * w ω) image x := by
  unfold conditionalWeight
  by_cases h : push ρ image x = 0
  · have hb := Lax342547.PushforwardWalsh.signed_push_bound ρ w image hρ hw x
    rw [h] at hb
    have hz := abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    simp [h, hz]
  · field_simp

/--
---
conclusion: Lax342547.PushforwardWalsh.image_walsh_bound
---
-/
theorem image_walsh_bound {ΩA ΩB I : Type} [Fintype ΩA] [Fintype ΩB]
    [Fintype I] [DecidableEq I]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (imageA : ΩA → I → Binary) (imageB : ΩB → I → Binary)
    (f : ΩA → ℝ) (g : ΩB → ℝ) (pA pB : ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1)
    (hcapA : ∀ x, push α imageA x ≤ pA) (hcapB : ∀ y, push β imageB y ≤ pB)
    (hf : ∀ a, |f a| ≤ 1) (hg : ∀ b, |g b| ≤ 1) :
    |∑ a, ∑ b, α a * β b * f a * g b * phase (imageA a) (imageB b)| ≤
      Real.sqrt ((2 : ℝ) ^ Fintype.card I * pA * pB) := by
  classical
  have h := Lax342547.Walsh.subprobability_dot_bound
    (push α imageA) (push β imageB)
    (conditionalWeight α f imageA) (conditionalWeight β g imageB) pA pB
    (fun x => ⟨Lax342547.PushforwardWalsh.push_nonneg α imageA hα x, hcapA x⟩)
    (fun y => ⟨Lax342547.PushforwardWalsh.push_nonneg β imageB hβ y, hcapB y⟩)
    (by simpa only [Lax342547.PushforwardWalsh.push_total] using hαsum) (by simpa only [Lax342547.PushforwardWalsh.push_total] using hβsum)
    (Lax342547.PushforwardWalsh.conditional_weight_bound α f imageA hα hf) (Lax342547.PushforwardWalsh.conditional_weight_bound β g imageB hβ hg)
  have he : (∑ x, ∑ y, push α imageA x * push β imageB y * conditionalWeight α f imageA x *
      conditionalWeight β g imageB y * phase x y) =
      ∑ a, ∑ b, α a * β b * f a * g b * phase (imageA a) (imageB b) := by
    have hh (x y : I → Binary) :
        push α imageA x * push β imageB y * conditionalWeight α f imageA x *
          conditionalWeight β g imageB y * phase x y =
        push (fun a => α a * f a) imageA x * push (fun b => β b * g b) imageB y * phase x y := by
      rw [← Lax342547.PushforwardWalsh.conditional_weight_reconstruction α f imageA hα hf x,
        ← Lax342547.PushforwardWalsh.conditional_weight_reconstruction β g imageB hβ hg y]
      ring
    simp only [hh]
    have hinner (x : I → Binary) :
        (∑ y, push (fun a => α a * f a) imageA x * push (fun b => β b * g b) imageB y * phase x y) =
        ∑ b, push (fun a => α a * f a) imageA x * (β b * g b) * phase x (imageB b) := by
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [Lax342547.PushforwardWalsh.push_integral]
      simp only [mul_assoc]
    simp only [hinner]
    rw [Finset.sum_comm]
    have houter (b : ΩB) :
        (∑ x, push (fun a => α a * f a) imageA x * (β b * g b) * phase x (imageB b)) =
        ∑ a, α a * f a * (β b * g b) * phase (imageA a) (imageB b) := by
      simp only [mul_assoc]
      rw [Lax342547.PushforwardWalsh.push_integral]
      simp only [mul_assoc]
    simp only [houter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he] at h
  exact h

end Lax342547Proofs.PushforwardWalsh
