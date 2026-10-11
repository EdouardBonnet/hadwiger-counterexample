import Lax342547.RawBatchComparison
import Lax342547Proofs.JoinedGramOrbits
import Lax342547.ChannelColumns
import Lax342547.ConditionedMixing
import Lax342547.CrossGramBasis
import Lax342547.FiniteSampling
import Lax342547.GramOrbitDensity
import Lax342547.JoinedGramOrbits
import Lax342547.JointGramInjection
import Lax342547.PushforwardWalsh
import Lax342547.RealCellLaws
import Lax342547.RetainedImages
import Lax342547Proofs.FiniteLinearLaw

namespace Lax342547Proofs.RawBatchComparison
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.RawBatchComparison
open Lax342547.GramOrbitDensity Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

theorem map_pair_apply {α β X Y : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → X) (g : β → Y) (z : X × Y) :
    (PMF.uniformOfFintype (α × β)).map (fun a => (f a.1,g a.2)) z =
      (PMF.uniformOfFintype α).map f z.1*(PMF.uniformOfFintype β).map g z.2 := by
  classical
  let e : {a : α × β // (f a.1,g a.2) = z} ≃
      ({a : α // f a = z.1} × {b : β // g b = z.2}) := {
    toFun := fun a => (⟨a.val.1,congrArg Prod.fst a.property⟩,⟨a.val.2,congrArg Prod.snd a.property⟩)
    invFun := fun a => ⟨(a.1.val,a.2.val),Prod.ext a.1.property a.2.property⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  simp_rw [FiniteLinearLaw.map_uniform_apply,Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  exact ENNReal.mul_div_mul_comm (Or.inr (by simp)) (Or.inl (by simp))

theorem weights_filter {Ω : Type} [Fintype Ω] (p : PMF Ω) (C : Ω → Prop)
    (h : ∃ x ∈ {x | C x},x ∈ p.support) (x : Ω) :
    weights (p.filter {x | C x} h) x = conditionalLaw (weights p) C x := by
  classical
  rw [weights,PMF.filter_apply,← PMF.toOuterMeasure_apply,ENNReal.toReal_mul,
    ENNReal.toReal_inv,← Lax342547.RealCellLaws.event_mass]
  by_cases hx : C x <;> simp [hx,Set.indicator,conditionalLaw,weights,div_eq_mul_inv]

theorem conditional_integral_push {Ω X : Type} [Fintype Ω] [Fintype X]
    (ρ : Ω → ℝ) (f : Ω → X) (C : X → Prop) (test : X → ℝ) :
    (∑ x,conditionalLaw (push ρ f) C x*test x) =
      ∑ ω,conditionalLaw ρ (fun ω => C (f ω)) ω*test (f ω) := by
  classical
  have hm := Lax342547.ChannelColumns.push_cell_mass ρ f C
  have hi := Lax342547.PushforwardWalsh.push_integral ρ f (fun x => if C x then test x else 0)
  simp only [mul_ite,mul_zero] at hi
  simp only [conditionalLaw,ite_mul,zero_mul,div_mul_eq_mul_div]
  simp only [← Finset.sum_div]
  rw [hi,hm]

theorem cell_nested {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C D : Ω → Prop) :
    cellMass (conditionalLaw ρ C) D = cellMass ρ (fun x => C x ∧ D x)/cellMass ρ C := by
  classical
  simp only [cellMass,conditionalLaw]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hC : C x <;> by_cases hD : D x <;> simp [hC,hD]

theorem nested_law {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C D : Ω → Prop)
    (hC : cellMass ρ C ≠ 0) :
    conditionalLaw (conditionalLaw ρ C) D = conditionalLaw ρ (fun x => C x ∧ D x) := by
  classical
  funext x
  rw [conditionalLaw,cell_nested]
  by_cases hc : C x <;> by_cases hd : D x <;>
    simp [hc,hd,conditionalLaw,div_div_div_cancel_right₀ hC]

theorem nested_deletion {Ω : Type} [Fintype Ω] (ρ test : Ω → ℝ) (C D : Ω → Prop)
    (hρ : Lax342547.RelativeEntropy.Probability ρ) (htest : ∀ x,|test x| ≤ 1)
    (hCD : 0 < cellMass ρ (fun x => C x ∧ D x)) :
    |(∑ x,conditionalLaw ρ (fun x => C x ∧ D x) x*test x)-
      (∑ x,conditionalLaw ρ C x*test x)| ≤
        2*(cellMass ρ (fun x => C x ∧ ¬ D x)/cellMass ρ C) := by
  classical
  have hC : 0 < cellMass ρ C := hCD.trans_le
    (Lax342547.FiniteSampling.cell_mass_mono ρ _ C hρ.1 (fun _ h => h.1))
  have hp : Lax342547.RelativeEntropy.Probability (conditionalLaw ρ C) :=
    ⟨Lax342547.RetainedImages.conditional_law_nonneg ρ C hρ.1,Lax342547.RetainedImages.conditional_law_total ρ C hC⟩
  have hD : 0 < cellMass (conditionalLaw ρ C) D := by rw [cell_nested]; positivity
  have hh := Lax342547.ConditionedMixing.bounded_integral_deletion (conditionalLaw ρ C) test D hp htest hD
  have hs : cellMass (conditionalLaw ρ C) D+cellMass (conditionalLaw ρ C) (fun x => ¬ D x) = 1 := by
    unfold cellMass
    rw [← Finset.sum_add_distrib]
    convert hp.2 using 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases hd : D x <;> simp [hd]
  have he : (∑ x,if D x then conditionalLaw ρ C x*test x else 0)/cellMass (conditionalLaw ρ C) D =
      ∑ x,conditionalLaw ρ (fun x => C x ∧ D x) x*test x := by
    rw [← nested_law ρ C D (ne_of_gt hC)]
    simp only [conditionalLaw,ite_mul,zero_mul,div_mul_eq_mul_div,← Finset.sum_div]
  rw [he] at hh
  have ht : 1-cellMass (conditionalLaw ρ C) D = cellMass (conditionalLaw ρ C) (fun x => ¬ D x) := by linarith
  rw [ht,cell_nested] at hh
  exact hh

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]


theorem reference_weights (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit N G)] [Nonempty (Orbit N H)]
    (z : (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary)) :
    weights ((PMF.uniformOfFintype (Orbit N G × Orbit N H)).map (flat G H)) z =
      batchLaw G z.1*batchLaw H z.2 := by
  unfold Lax342547.RawBatchComparison.flat batchLaw weights
  rw [map_pair_apply (fun z : Orbit N G => batchEquiv z.val) (fun z : Orbit N H => batchEquiv z.val) z]
  exact ENNReal.toReal_mul



theorem flat_compatible (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary) (z : Orbit (Fin n) G × Orbit (Fin n) H) :
    Lax342547.JoinedGramOrbits.Compatible G H A B z ↔
      Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n (flat G H z) = target A B ∧
        Lax342547.JointGramInjection.Good (flat G H z) := by
  have hb := Lax342547.CrossGramBasis.mutual_gram_bits n (flat G H z)
  have he : Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n (flat G H z) = target A B ↔
      z.1.val.1.transpose*z.2.val.2 = A ∧ z.2.val.1.transpose*z.1.val.2 = B := by
    constructor
    · intro h
      constructor
      · ext i l
        have hh := congrFun h (Sum.inl (i,l))
        rw [hb.1] at hh
        simpa [flat,batchEquiv,target,Matrix.mul_apply,Matrix.transpose_apply] using hh
      · ext k j
        have hh := congrFun h (Sum.inr (j,k))
        rw [hb.2] at hh
        simpa [flat,batchEquiv,target,Matrix.mul_apply,Matrix.transpose_apply,mul_comm] using hh
    · rintro ⟨hA,hB⟩
      funext s
      rcases s with ⟨i,l⟩ | ⟨j,k⟩
      · rw [hb.1]
        have hh := congrArg (fun M => M i l) hA
        simpa [flat,batchEquiv,target,Matrix.mul_apply,Matrix.transpose_apply] using hh
      · rw [hb.2]
        have hh := congrArg (fun M => M k j) hB
        simpa [flat,batchEquiv,target,Matrix.mul_apply,Matrix.transpose_apply,mul_comm] using hh
  rw [he]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ (_ ∧ _)
  tauto

/--
---
conclusion: Lax342547.RawBatchComparison.union_conditional_integral
---
-/
theorem union_conditional_integral (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (test : ((Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary)) → ℝ) :
    (∑ z : Orbit (Fin n) (Matrix.fromBlocks G A B H),
      weights (PMF.uniformOfFintype _) z*test (Lax342547.JointGramInjection.ambientEquiv.symm z.val)) =
    ∑ x,conditionalLaw (fun x => batchLaw G x.1*batchLaw H x.2)
      (fun x => Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n x = target A B ∧
        Lax342547.JointGramInjection.Good x) x*test x := by
  classical
  let C := Lax342547.JoinedGramOrbits.Compatible (N := Fin n) G H A B
  let : Nonempty {z : Orbit (Fin n) G × Orbit (Fin n) H // C z} :=
    ⟨JoinedGramOrbits.equiv G H A B (Classical.choice inferInstance)⟩
  let p := PMF.uniformOfFintype (Orbit (Fin n) G × Orbit (Fin n) H)
  have hc : ∃ z ∈ {z : Orbit (Fin n) G × Orbit (Fin n) H | C z},z ∈ p.support := by
    obtain ⟨z,hz⟩ := Classical.choice (inferInstance : Nonempty {z : Orbit (Fin n) G × Orbit (Fin n) H // C z})
    exact ⟨z,hz,by simp [p]⟩
  have hu := Lax342547.JoinedGramOrbits.compatible_filter G H A B hc
  have hi := congrArg (fun q => ∑ x,weights q x*test (Lax342547.JointGramInjection.ambientEquiv.symm x)) hu
  simp_rw [Lax342547.ChannelColumns.pmf_weights_map] at hi
  rw [Lax342547.PushforwardWalsh.push_integral,Lax342547.PushforwardWalsh.push_integral] at hi
  simp only [weights_filter] at hi
  have he : (fun x => batchLaw G x.1*batchLaw H x.2) = push (weights p) (flat G H) := by
    funext x
    rw [← Lax342547.ChannelColumns.pmf_weights_map]
    exact (reference_weights G H x).symm
  rw [he,conditional_integral_push]
  have hC : (fun ω : Orbit (Fin n) G × Orbit (Fin n) H =>
      Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n (flat G H ω) = target A B ∧
      Lax342547.JointGramInjection.Good (flat G H ω)) = C := by
    funext z
    exact propext (flat_compatible n G H A B z).symm
  rw [hC]
  convert hi.symm using 1
  apply Finset.sum_congr rfl
  intro z _
  rfl

/--
---
conclusion: Lax342547.RawBatchComparison.union_test_comparison
---
-/
theorem union_test_comparison (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ z : Orbit (Fin n) (Matrix.fromBlocks G A B H),weights (PMF.uniformOfFintype _) z*
        (f (Lax342547.JointGramInjection.ambientEquiv.symm z.val).1*
          g (Lax342547.JointGramInjection.ambientEquiv.symm z.val).2))-
      (∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y)| ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
        ((((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n))+
          (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
            ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
            (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n))) := by
  classical
  let ρ := fun x : (Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary) =>
    batchLaw G x.1*batchLaw H x.2
  let C := fun x => Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n x = target A B
  let D := fun x : (Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary) =>
    Lax342547.JointGramInjection.Good x
  let test := fun x : (Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary) => f x.1*g x.2
  have hG := Lax342547.GramOrbitDensity.batch_probability (N := Fin n) G
  have hH := Lax342547.GramOrbitDensity.batch_probability (N := Fin n) H
  have hρ : Lax342547.RelativeEntropy.Probability ρ := by
    refine ⟨fun x => mul_nonneg (hG.1 _) (hH.1 _),?_⟩
    simp only [ρ,Fintype.sum_prod_type,← Finset.mul_sum,hH.2,mul_one,hG.2]
  have ht : ∀ x,|test x| ≤ 1 := by
    intro x
    exact (by dsimp [test]; rw [abs_mul]; exact (mul_le_mul (hf _) (hg _) (abs_nonneg _) zero_le_one).trans_eq (mul_one _))
  have htotal := Lax342547.RawBatchComparison.union_conditional_integral n G H A B (fun _ => 1)
  simp only [mul_one,Lax342547.RealCellLaws.weights_total] at htotal
  have hm : 0 < cellMass ρ (fun x => C x ∧ D x) := by
    have hn : 0 ≤ cellMass ρ (fun x => C x ∧ D x) := by
      unfold cellMass
      exact Finset.sum_nonneg (fun x _ => by split_ifs; exact hρ.1 x; rfl)
    by_contra hh
    have hz : cellMass ρ (fun x => C x ∧ D x) = 0 := le_antisymm (le_of_not_gt hh) hn
    have he : ∑ x,conditionalLaw ρ (fun x => C x ∧ D x) x = 0 := by
      simp [conditionalLaw,hz]
    change 1 = ∑ x,conditionalLaw ρ (fun x => C x ∧ D x) x at htotal
    rw [he] at htotal
    norm_num at htotal
  have hdel := nested_deletion ρ test C D hρ ht hm
  have hbad := Lax342547.JointGramInjection.conditioned_reference_failure n G H (target A B) hN₁ hN₂ hsmall
  have hmix := Lax342547.GramOrbitDensity.mutual_gram_comparison n G H f g (target A B) hN₁ hN₂ hf hg hsmall
  have he : Lax342547.FourierTests.patternMass (fun x => ρ x*test x)
      (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) (target A B)/
      Lax342547.FourierTests.patternMass ρ (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) (target A B) =
      ∑ x,conditionalLaw ρ C x*test x := by
    simp only [Lax342547.FourierTests.patternMass,conditionalLaw,cellMass,C,ite_mul,zero_mul,
      div_mul_eq_mul_div,← Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  change |Lax342547.FourierTests.patternMass (fun x => ρ x*test x)
      (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) (target A B)/
      Lax342547.FourierTests.patternMass ρ (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) (target A B)-
      (∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y)| ≤ _ at hmix
  rw [he] at hmix
  have hb : cellMass ρ (fun x => C x ∧ ¬ D x)/cellMass ρ C ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)*
        (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
          (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n)) := by
    simpa only [ρ,C,D,Lax342547.FourierTests.patternMass,cellMass] using hbad
  rw [Lax342547.RawBatchComparison.union_conditional_integral n G H A B test]
  have hh := (abs_sub_le (∑ x,conditionalLaw ρ (fun x => C x ∧ D x) x*test x)
    (∑ x,conditionalLaw ρ C x*test x) ((∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y))).trans
      (add_le_add (hdel.trans (mul_le_mul_of_nonneg_left hb (by norm_num))) hmix)
  convert hh using 1 <;> try rfl
  rw [show Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2 =
    (Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)+1 from rfl,pow_succ]
  ring

end
end Lax342547Proofs.RawBatchComparison
