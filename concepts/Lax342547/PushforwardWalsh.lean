import Lax342547.Walsh

/-!
---
title: Walsh bounds for independent image laws and separated phases
type: lemma
---
Image pushforwards and conditional bounded weights translate the finite Walsh bound to arbitrary orientation laws, preserving separate phases from frozen vectors.
-/

namespace Lax342547.PushforwardWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def push {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X) (x : X) : ℝ := by
  classical
  exact ∑ ω, if image ω = x then ρ ω else 0

axiom push_nonneg {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X)
    (hρ : ∀ ω, 0 ≤ ρ ω) (x : X) : 0 ≤ push ρ image x

axiom push_total {Ω X : Type} [Fintype Ω] [Fintype X] (ρ : Ω → ℝ) (image : Ω → X) :
    ∑ x, push ρ image x = ∑ ω, ρ ω

axiom push_integral {Ω X : Type} [Fintype Ω] [Fintype X]
    (ρ : Ω → ℝ) (image : Ω → X) (f : X → ℝ) :
    ∑ x, push ρ image x * f x = ∑ ω, ρ ω * f (image ω)

axiom signed_push_bound {Ω X : Type} [Fintype Ω] (ρ w : Ω → ℝ) (image : Ω → X)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hw : ∀ ω, |w ω| ≤ 1) (x : X) :
    |push (fun ω => ρ ω * w ω) image x| ≤ push ρ image x

noncomputable def conditionalWeight {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (x : X) : ℝ :=
  push (fun ω => ρ ω * w ω) image x / push ρ image x

axiom conditional_weight_bound {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hw : ∀ ω, |w ω| ≤ 1) (x : X) : |conditionalWeight ρ w image x| ≤ 1

axiom conditional_weight_reconstruction {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hw : ∀ ω, |w ω| ≤ 1) (x : X) :
    push ρ image x * conditionalWeight ρ w image x =
      push (fun ω => ρ ω * w ω) image x

axiom image_walsh_bound {ΩA ΩB I : Type} [Fintype ΩA] [Fintype ΩB]
    [Fintype I] [DecidableEq I]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (imageA : ΩA → I → Binary) (imageB : ΩB → I → Binary)
    (f : ΩA → ℝ) (g : ΩB → ℝ) (pA pB : ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1)
    (hcapA : ∀ x, push α imageA x ≤ pA) (hcapB : ∀ y, push β imageB y ≤ pB)
    (hf : ∀ a, |f a| ≤ 1) (hg : ∀ b, |g b| ≤ 1) :
    |∑ a, ∑ b, α a * β b * f a * g b * phase (imageA a) (imageB b)| ≤
      Real.sqrt ((2 : ℝ) ^ Fintype.card I * pA * pB)

end Lax342547.PushforwardWalsh
