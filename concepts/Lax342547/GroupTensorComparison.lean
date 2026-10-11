import Lax342547.RawFrameComparison

/-!
---
title: Two-batch comparison across independent component groups
type: definition and theorem
---
Replacing one independent group at a time adds its bounded separate-test
error. The global tests may depend arbitrarily on all groups, and the two
observations inside each group retain their full joint dependence. Different
groups may have different finite state spaces and column counts.
-/

namespace Lax342547.GroupTensorComparison
noncomputable section
open Lax342547.RelativeEntropy
open scoped BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)]

def mean (ρ : ∀ i,X i × Y i → ℝ) (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ) : ℝ :=
  ∑ z : ∀ i,X i × Y i,(∏ i,ρ i (z i))*f (fun i => (z i).1)*g (fun i => (z i).2)

axiom product_comparison (ρ σ : ∀ j,X j × Y j → ℝ)
    (hρ : ∀ j,Probability (ρ j)) (hσ : ∀ j,Probability (σ j)) (ε : ι → ℝ)
    (hc : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-(∑ z : X i × Y i,σ i z*f z.1*g z.2)| ≤ ε i)
    (f : (∀ j,X j) → ℝ) (g : (∀ j,Y j) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |mean ρ f g-mean σ f g| ≤ ∑ i,ε i

axiom reference_product_comparison (ρ : ∀ i,X i × Y i → ℝ)
    (α : ∀ i,X i → ℝ) (β : ∀ i,Y i → ℝ)
    (hρ : ∀ i,Probability (ρ i)) (hα : ∀ i,Probability (α i)) (hβ : ∀ i,Probability (β i))
    (ε : ι → ℝ)
    (hc : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-
        (∑ x,α i x*f x)*(∑ y,β i y*g y)| ≤ ε i)
    (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |mean ρ f g-(∑ x,(∏ i,α i (x i))*f x)*(∑ y,(∏ i,β i (y i))*g y)| ≤ ∑ i,ε i

end
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y Ω : ι → Type} [∀ i,Fintype (Ω i)] [∀ i,Nonempty (Ω i)]
open Lax342547.RealCellLaws

axiom uniform_group_comparison [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] (x : ∀ i,Ω i → X i) (y : ∀ i,Ω i → Y i)
    (ε : ι → ℝ)
    (hc : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ o : Ω i,weights (PMF.uniformOfFintype _) o*(f (x i o)*g (y i o)))-
        (∑ o : Ω i,weights (PMF.uniformOfFintype _) o*f (x i o))*
        (∑ o : Ω i,weights (PMF.uniformOfFintype _) o*g (y i o))| ≤ ε i)
    (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |(∑ o : ∀ i,Ω i,weights (PMF.uniformOfFintype _) o*
        (f (fun i => x i (o i))*g (fun i => y i (o i))))-
      (∑ o : ∀ i,Ω i,weights (PMF.uniformOfFintype _) o*f (fun i => x i (o i)))*
      (∑ o : ∀ i,Ω i,weights (PMF.uniformOfFintype _) o*g (fun i => y i (o i)))| ≤ ∑ i,ε i

end
end Lax342547.GroupTensorComparison
