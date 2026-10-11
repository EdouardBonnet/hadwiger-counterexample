import Lax342547.GroupTensorComparison
import Lax342547.ChannelColumns
import Lax342547.PushforwardWalsh
import Lax342547.RealCellLaws
import Lax342547Proofs.FiniteUniform

namespace Lax342547Proofs.GroupTensorComparison
noncomputable section
open Lax342547.GroupTensorComparison
open Lax342547.RelativeEntropy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)]


theorem sum_split_at {Ω : ι → Type} [∀ i,Fintype (Ω i)] (i : ι) (T : (∀ j,Ω j) → ℝ) :
    (∑ z,T z) = ∑ r : ∀ j : {j // j ≠ i},Ω j,∑ a : Ω i,T ((Equiv.piSplitAt i Ω).symm (a,r)) := by
  rw [← (Equiv.piSplitAt i Ω).symm.sum_comp T,Fintype.sum_prod_type,Finset.sum_comm]

theorem prod_split_at (i : ι) (h : ι → ℝ) : (∏ j,h j) = h i*(∏ j : {j // j ≠ i},h j)  := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp [eq_comm]) (fun j => h j)

theorem one_group_comparison (i : ι) (ρ σ : ∀ j,X j × Y j → ℝ)
    (hρ : ∀ j,Probability (ρ j)) (hother : ∀ j,j ≠ i → ρ j = σ j)
    (ε : ℝ)
    (hc : ∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-(∑ z : X i × Y i,σ i z*f z.1*g z.2)| ≤ ε)
    (f : (∀ j,X j) → ℝ) (g : (∀ j,Y j) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |mean ρ f g-mean σ f g| ≤ ε := by
  classical
  let Ω := fun j => X j × Y j
  let weight := fun r : ∀ j : {j // j ≠ i},Ω j => ∏ j : {j // j ≠ i},ρ j (r j)
  have hn r : 0 ≤ weight r := Finset.prod_nonneg (fun j _ => (hρ j).1 _)
  have ht : ∑ r,weight r = 1 := by
    dsimp [weight]
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro j _
    exact (hρ j).2
  let F := fun r : ∀ j : {j // j ≠ i},Ω j => fun x : X i =>
    f ((Equiv.piSplitAt i X).symm (x,fun j => (r j).1))
  let G := fun r : ∀ j : {j // j ≠ i},Ω j => fun y : Y i =>
    g ((Equiv.piSplitAt i Y).symm (y,fun j => (r j).2))
  have he (μ : ∀ j,Ω j → ℝ) (hμ : ∀ j,j ≠ i → μ j = ρ j) :
      mean μ f g = ∑ r,weight r*(∑ a : Ω i,μ i a*F r a.1*G r a.2) := by
    unfold mean
    rw [sum_split_at i,Finset.sum_congr rfl (fun r _ => ?_)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [prod_split_at i]
    have hw : (∏ j : {j // j ≠ i},μ j ((Equiv.piSplitAt i Ω).symm (a,r) j)) = weight r := by
      change _ = ∏ j : {j // j ≠ i},ρ j (r j)
      apply Finset.prod_congr rfl
      intro j _
      rw [hμ j j.property]
      simp [Equiv.piSplitAt,j.property]
    rw [hw]
    have hx : (fun j => ((Equiv.piSplitAt i Ω).symm (a,r) j).1) =
        (Equiv.piSplitAt i X).symm (a.1,fun j => (r j).1) := by
      funext j
      by_cases h : j = i
      · subst j; simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt,h]
    have hy : (fun j => ((Equiv.piSplitAt i Ω).symm (a,r) j).2) =
        (Equiv.piSplitAt i Y).symm (a.2,fun j => (r j).2) := by
      funext j
      by_cases h : j = i
      · subst j; simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt,h]
    have hi : (Equiv.piSplitAt i Ω).symm (a,r) i = a := by simp [Equiv.piSplitAt]
    rw [hi,hx,hy]
    dsimp [F,G]
    ring
  rw [he ρ (fun _ _ => rfl),he σ (fun j hj => (hother j hj).symm),← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ r,|weight r*((∑ a : Ω i,ρ i a*F r a.1*G r a.2)-
      (∑ a : Ω i,σ i a*F r a.1*G r a.2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r,weight r*ε := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul,abs_of_nonneg (hn r)]
      exact mul_le_mul_of_nonneg_left (hc (F r) (G r) (fun _ => hf _) (fun _ => hg _)) (hn r)
    _ = ε := by rw [← Finset.sum_mul,ht,one_mul]

/--
---
conclusion: Lax342547.GroupTensorComparison.product_comparison
---
-/
theorem product_comparison (ρ σ : ∀ j,X j × Y j → ℝ)
    (hρ : ∀ j,Probability (ρ j)) (hσ : ∀ j,Probability (σ j)) (ε : ι → ℝ)
    (hc : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-(∑ z : X i × Y i,σ i z*f z.1*g z.2)| ≤ ε i)
    (f : (∀ j,X j) → ℝ) (g : (∀ j,Y j) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |mean ρ f g-mean σ f g| ≤ ∑ i,ε i := by
  classical
  let law := fun S : Finset ι => fun j => if j ∈ S then σ j else ρ j
  have hs : ∀ S : Finset ι,|mean (law S) f g-mean ρ f g| ≤ ∑ i ∈ S,ε i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have he : law ∅ = ρ := by funext j; simp [law]
      rw [he]
      simp
    | @insert i S hi ih =>
      have hp : ∀ j,Probability (law S j) := by
        intro j
        dsimp [law]
        split_ifs
        · exact hσ j
        · exact hρ j
      have ho : ∀ j,j ≠ i → law S j = law (insert i S) j := by
        intro j hj
        simp [law,hj]
      have hcut : ∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
          |(∑ z : X i × Y i,law S i z*f z.1*g z.2)-
            (∑ z : X i × Y i,law (insert i S) i z*f z.1*g z.2)| ≤ ε i := by
        simpa only [law,if_neg hi,Finset.mem_insert_self,if_true] using hc i
      have hh := one_group_comparison i (law S) (law (insert i S)) hp ho (ε i) hcut f g hf hg
      rw [abs_sub_comm] at hh
      rw [Finset.sum_insert hi]
      exact (abs_sub_le (mean (law (insert i S)) f g) (mean (law S) f g) (mean ρ f g)).trans
        (add_le_add hh ih)
  have he : law Finset.univ = σ := by funext j; simp [law]
  have hh := hs Finset.univ
  rw [he,abs_sub_comm] at hh
  simpa using hh

def arraysEquiv : (∀ i,X i × Y i) ≃ ((∀ i,X i) × (∀ i,Y i)) where
  toFun z := (fun i => (z i).1,fun i => (z i).2)
  invFun z := fun i => (z.1 i,z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem mean_product (α : ∀ i,X i → ℝ) (β : ∀ i,Y i → ℝ)
    (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ) :
    mean (fun i z => α i z.1*β i z.2) f g =
      (∑ x,(∏ i,α i (x i))*f x)*(∑ y,(∏ i,β i (y i))*g y) := by
  unfold mean
  rw [← (arraysEquiv (X := X) (Y := Y)).symm.sum_comp]
  change (∑ z : (∀ i,X i) × (∀ i,Y i),(∏ i,α i (z.1 i)*β i (z.2 i))*f z.1*g z.2) = _
  simp_rw [Finset.prod_mul_distrib]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/--
---
conclusion: Lax342547.GroupTensorComparison.reference_product_comparison
---
-/
theorem reference_product_comparison (ρ : ∀ i,X i × Y i → ℝ)
    (α : ∀ i,X i → ℝ) (β : ∀ i,Y i → ℝ)
    (hρ : ∀ i,Probability (ρ i)) (hα : ∀ i,Probability (α i)) (hβ : ∀ i,Probability (β i))
    (ε : ι → ℝ)
    (hc : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-
        (∑ x,α i x*f x)*(∑ y,β i y*g y)| ≤ ε i)
    (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |mean ρ f g-(∑ x,(∏ i,α i (x i))*f x)*(∑ y,(∏ i,β i (y i))*g y)| ≤ ∑ i,ε i := by
  let σ : ∀ i,X i × Y i → ℝ := fun i z => α i z.1*β i z.2
  have hp : ∀ i,Probability (σ i) := by
    intro i
    refine ⟨fun z => mul_nonneg ((hα i).1 _) ((hβ i).1 _),?_⟩
    simp only [σ,Fintype.sum_prod_type,← Finset.mul_sum,(hβ i).2,mul_one,(hα i).2]
  have hh : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-(∑ z : X i × Y i,σ i z*f z.1*g z.2)| ≤ ε i := by
    intro i f g hf hg
    have he : (∑ z : X i × Y i,σ i z*f z.1*g z.2) =
        (∑ x,α i x*f x)*(∑ y,β i y*g y) := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      dsimp [σ]
      ring
    rw [he]
    exact hc i f g hf hg
  have ht := Lax342547.GroupTensorComparison.product_comparison ρ σ hρ hp ε hh f g hf hg
  rw [mean_product] at ht
  exact ht

end
noncomputable section
open Lax342547.GroupTensorComparison Lax342547.RelativeEntropy
open scoped BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y Ω : ι → Type} [∀ i,Fintype (Ω i)] [∀ i,Nonempty (Ω i)]
open Lax342547.RealCellLaws

theorem pi_uniform_integral [∀ i,Fintype (X i)] (x : ∀ i,Ω i → X i) (test : (∀ i,X i) → ℝ) :
    (∑ z,(∏ i,weights ((PMF.uniformOfFintype (Ω i)).map (x i)) (z i))*test z) =
      ∑ o : ∀ i,Ω i,weights (PMF.uniformOfFintype _) o*test (fun i => x i (o i)) := by
  have hp (z : ∀ i,X i) :
      weights ((PMF.uniformOfFintype (∀ i,Ω i)).map (fun o i => x i (o i))) z =
        ∏ i,weights ((PMF.uniformOfFintype (Ω i)).map (x i)) (z i) := by
    rw [weights,FiniteUniform.map_pi_apply,ENNReal.toReal_prod]
    rfl
  have hh := Lax342547.PushforwardWalsh.push_integral (weights (PMF.uniformOfFintype (∀ i,Ω i)))
    (fun o i => x i (o i)) test
  simp_rw [← Lax342547.ChannelColumns.pmf_weights_map,hp] at hh
  exact hh

/--
---
conclusion: Lax342547.GroupTensorComparison.uniform_group_comparison
---
-/
theorem uniform_group_comparison [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] (x : ∀ i,Ω i → X i) (y : ∀ i,Ω i → Y i)
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
      (∑ o : ∀ i,Ω i,weights (PMF.uniformOfFintype _) o*g (fun i => y i (o i)))| ≤ ∑ i,ε i := by
  let ρ : ∀ i,X i × Y i → ℝ := fun i =>
    weights ((PMF.uniformOfFintype (Ω i)).map (fun o => (x i o,y i o)))
  let α : ∀ i,X i → ℝ := fun i => weights ((PMF.uniformOfFintype (Ω i)).map (x i))
  let β : ∀ i,Y i → ℝ := fun i => weights ((PMF.uniformOfFintype (Ω i)).map (y i))
  have hρ : ∀ i,Probability (ρ i) := fun _ => ⟨Lax342547.RealCellLaws.weights_nonneg _,Lax342547.RealCellLaws.weights_total _⟩
  have hα : ∀ i,Probability (α i) := fun _ => ⟨Lax342547.RealCellLaws.weights_nonneg _,Lax342547.RealCellLaws.weights_total _⟩
  have hβ : ∀ i,Probability (β i) := fun _ => ⟨Lax342547.RealCellLaws.weights_nonneg _,Lax342547.RealCellLaws.weights_total _⟩
  have hh : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-
        (∑ z,α i z*f z)*(∑ z,β i z*g z)| ≤ ε i := by
    intro i f g hf hg
    dsimp [ρ,α,β]
    simp_rw [mul_assoc,Lax342547.ChannelColumns.pmf_weights_map]
    rw [Lax342547.PushforwardWalsh.push_integral,Lax342547.PushforwardWalsh.push_integral,Lax342547.PushforwardWalsh.push_integral]
    exact hc i f g hf hg
  have ht := Lax342547.GroupTensorComparison.reference_product_comparison ρ α β hρ hα hβ ε hh f g hf hg
  have hj := pi_uniform_integral (fun i o => (x i o,y i o))
    (fun z : ∀ i,X i × Y i => f (fun i => (z i).1)*g (fun i => (z i).2))
  have hx := pi_uniform_integral x f
  have hy := pi_uniform_integral y g
  simp only [← mul_assoc] at hj
  change mean ρ f g = _ at hj
  change (∑ z,(∏ i,α i (z i))*f z) = _ at hx
  change (∑ z,(∏ i,β i (z i))*g z) = _ at hy
  rw [hj,hx,hy] at ht
  simpa only [mul_assoc] using ht

end
end Lax342547Proofs.GroupTensorComparison
