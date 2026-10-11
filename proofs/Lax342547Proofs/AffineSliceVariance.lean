import Lax342547.AffineSliceVariance
import Lax342547Proofs.ConditionedAffineColumns
import Lax342547Proofs.RawGroupedComparison
import Lax342547Proofs.EmpiricalVariance

namespace Lax342547Proofs.AffineSliceVariance
noncomputable section
open Lax342547.AffineSliceVariance
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RawFrames
open Lax342547.RealCellLaws Lax342547.GramOrbitDensity Lax342547.RelativeEntropy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 theorem concatenation_injective {I J N : Type} [Fintype I] [Fintype J]
    (C : Matrix N I Binary) (D : Matrix N J Binary)
    (h : Function.Injective (fun v : (I → Binary) × (J → Binary) => C.mulVec v.1+D.mulVec v.2)) :
    Function.Injective (Matrix.fromCols C D).mulVec := by
  intro x y hxy
  have hp := h (a₁ := (x ∘ Sum.inl,x ∘ Sum.inr)) (a₂ := (y ∘ Sum.inl,y ∘ Sum.inr))
    (by simpa only [Matrix.fromCols_mulVec] using hxy)
  funext s
  cases s with
  | inl i => exact congrFun (congrArg Prod.fst hp) i
  | inr j => exact congrFun (congrArg Prod.snd hp) j

/--
---
conclusion: Lax342547.AffineSliceVariance.reference_mean
---
-/
theorem reference_mean {S B H D : Type} [Fintype S] [DecidableEq S]
    [Fintype B] [Fintype H] [Fintype D] [DecidableEq D]
    (n : ℕ) (E : S → Matrix B B Binary) (G : S → Matrix D D Binary)
    [∀ s,Nonempty (Frame B H (Fin n) (E s))] [∀ s,Nonempty (Orbit (Fin n) (G s))]
    (C : Matrix B D Binary) (hC : Function.Injective C.mulVec)
    (hG : ∀ s,C.transpose*E s*C = G s)
    (test : (S → (Fin n × (D ⊕ D) → Binary)) → ℝ) :
    (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
      test (fun s => batchEquiv ((o s).P*C,(o s).Q*C))) =
    ∑ z : ∀ s,Orbit (Fin n) (G s),weights (PMF.uniformOfFintype _) z*
      test (fun s => batchEquiv (z s).val) := by
  have hi := GroupTensorComparison.pi_uniform_integral
    (fun s (F : Frame B H (Fin n) (E s)) => batchEquiv (F.P*C,F.Q*C)) test
  have hj := GroupTensorComparison.pi_uniform_integral
    (fun s (z : Orbit (Fin n) (G s)) => batchEquiv z.val) test
  have he (s : S) :
      (PMF.uniformOfFintype (Frame B H (Fin n) (E s))).map
        (fun F => batchEquiv (F.P*C,F.Q*C)) =
      (PMF.uniformOfFintype (Orbit (Fin n) (G s))).map (fun z => batchEquiv z.val) := by
    let : Nonempty (Orbit (Fin n) (C.transpose*E s*C)) :=
      ⟨primalTuple (H := H) (E := E s) C C hC hC (Classical.choice inferInstance)⟩
    have hp := congrArg (fun p => p.map Subtype.val)
      (FrameTuples.primal_uniform (H := H) (N := Fin n) (E := E s) C C hC hC)
    rw [PMF.map_comp] at hp
    simp only [Function.comp_def,primalTuple] at hp
    have hp' := hp.trans (RawFrameComparison.orbit_uniform_congr (N := Fin n) (hG s))
    have hflat := congrArg (fun p => p.map batchEquiv) hp'
    rw [PMF.map_comp,PMF.map_comp] at hflat
    exact hflat
  simp_rw [he] at hi
  exact hi.symm.trans hj

 theorem probability_test_bound {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (hρ : Probability ρ)
    (test : Ω → ℝ) (ht : ∀ x,|test x| ≤ 1) : |∑ x,ρ x*test x| ≤ 1 := by
  calc
    _ ≤ ∑ x,|ρ x*test x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x,ρ x := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul,abs_of_nonneg (hρ.1 x)]
      exact (mul_le_mul_of_nonneg_left (ht x) (hρ.1 x)).trans_eq (mul_one _)
    _ = 1 := hρ.2

/--
---
conclusion: Lax342547.AffineSliceVariance.coefficient_variance
---
-/
theorem coefficient_variance {S B H D A : Type} [Fintype S] [DecidableEq S]
    [Fintype B] [Fintype H] [Fintype D] [DecidableEq D] [Fintype A]
    (n : ℕ) (E : S → Matrix B B Binary) (G : S → Matrix D D Binary)
    [∀ s,Nonempty (Frame B H (Fin n) (E s))] [∀ s,Nonempty (Orbit (Fin n) (G s))]
    (C : A → Matrix B D Binary) (κ : A → ℝ) (hκ : Probability κ)
    (hGram : ∀ a,κ a ≠ 0 → ∀ s,(C a).transpose*E s*C a = G s)
    (test : (S → (Fin n × (D ⊕ D) → Binary)) → ℝ) (htest : ∀ z,|test z| ≤ 1)
    (δ : ℝ) (hbad : Lax342547.RetainedImages.cellMass (fun ab : A × A => κ ab.1*κ ab.2)
      (fun ab => ¬ Function.Injective (Matrix.fromCols (C ab.1) (C ab.2)).mulVec) ≤ δ)
    (hN : Fintype.card D+Fintype.card D+1 ≤ n)
    (hsmall : ((2 : ℝ)^(Fintype.card D*Fintype.card D+2))*
        ((2 : ℝ)^(Fintype.card D*Fintype.card D+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots D D D D)+1)) :
    (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
      ((∑ a,κ a*test (fun s => batchEquiv ((o s).P*C a,(o s).Q*C a)))-
        referenceMean n G test)^2) ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound n D D D D+4*δ := by
  classical
  let ρ := weights (PMF.uniformOfFintype (∀ s,Frame B H (Fin n) (E s)))
  let F := fun o : ∀ s,Frame B H (Fin n) (E s) => fun a : A =>
    test (fun s => batchEquiv ((o s).P*C a,(o s).Q*C a))
  let m := referenceMean n G test
  let good := fun a b : A => κ a ≠ 0 ∧ κ b ≠ 0 ∧ Function.Injective (Matrix.fromCols (C a) (C b)).mulVec
  have hρ : Probability ρ := ⟨RealCellLaws.weights_nonneg _,RealCellLaws.weights_total _⟩
  have hm : |m| ≤ 1 := probability_test_bound _
    ⟨RealCellLaws.weights_nonneg _,RealCellLaws.weights_total _⟩ _ (fun _ => htest _)
  have hmean : ∀ a b,good a b → (∑ o,ρ o*F o a) = m ∧ (∑ o,ρ o*F o b) = m := by
    intro a b hgood
    have hCa : Function.Injective (C a).mulVec := by
      have he : (Matrix.fromCols (C a) (C b)).submatrix id Sum.inl = C a := rfl
      rw [← he]
      exact JoinedGramOrbits.left_injective _ hgood.2.2
    have hCb : Function.Injective (C b).mulVec := by
      have he : (Matrix.fromCols (C a) (C b)).submatrix id Sum.inr = C b := rfl
      rw [← he]
      exact JoinedGramOrbits.right_injective _ hgood.2.2
    exact ⟨reference_mean (H := H) n E G (C a) hCa (hGram a hgood.1) test,
      reference_mean (H := H) n E G (C b) hCb (hGram b hgood.2.1) test⟩
  have hpair : ∀ a b,good a b → |(∑ o,ρ o*F o a*F o b)-m^2| ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound n D D D D := by
    intro a b hgood
    have hh := RawGroupedComparison.primal_groups (H := H) n E
      (fun _ => C a) (fun _ => C a) (fun _ => C b) (fun _ => C b)
      (fun _ => hgood.2.2) (fun _ => hgood.2.2) test test (fun _ => hN) (fun _ => hN) htest htest (fun _ => hsmall)
    have ha := (hmean a b hgood).1
    have hb := (hmean a b hgood).2
    change |(∑ o,ρ o*(F o a*F o b))-(∑ o,ρ o*F o a)*(∑ o,ρ o*F o b)| ≤ _ at hh
    rw [ha,hb] at hh
    simpa only [pow_two,mul_assoc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  have hb : Lax342547.RetainedImages.cellMass (fun ab : A × A => κ ab.1*κ ab.2)
      (fun ab => ¬ good ab.1 ab.2) ≤ δ := by
    have he : Lax342547.RetainedImages.cellMass (fun ab : A × A => κ ab.1*κ ab.2)
        (fun ab => ¬ good ab.1 ab.2) =
      Lax342547.RetainedImages.cellMass (fun ab : A × A => κ ab.1*κ ab.2)
        (fun ab => ¬ Function.Injective (Matrix.fromCols (C ab.1) (C ab.2)).mulVec) := by
      unfold Lax342547.RetainedImages.cellMass
      apply Finset.sum_congr rfl
      intro ab _
      by_cases ha : κ ab.1 = 0 <;> by_cases hb : κ ab.2 = 0 <;> simp [good,ha,hb]
    rw [he]
    exact hbad
  exact EmpiricalVariance.empirical_variance ρ κ F good m
    ((Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound n D D D D) δ hρ hκ
    (fun _ _ => htest _) hm (by unfold Lax342547.RawFrameComparison.errorBound; positivity) hmean hpair hb

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.AffineSliceIndependence
open Lax342547.RetainedImages

/--
---
conclusion: Lax342547.AffineSliceVariance.affine_slice_variance
---
-/
theorem affine_slice_variance {S H D : Type} [Fintype S] [DecidableEq S]
    [Fintype H] [Fintype D] [DecidableEq D] {k n b degree : ℕ}
    (N : ℕ) (sel : Fin b → Binary)
    (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option D) (Option D) Binary)
    [∀ i,Nonempty (Frame (Coordinate k n b degree) H (Fin N) (E i))]
    [∀ i,Nonempty (Orbit (Fin N) (G i))]
    (β : ℝ) (hβ : 0 < β)
    (hGram : β ≤ cellMass (weights (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary)))
      (GramEvent sel E G))
    (test : (S → (Fin N × (Option D ⊕ Option D) → Binary)) → ℝ) (htest : ∀ z,|test z| ≤ 1)
    (hN : Fintype.card (Option D)+Fintype.card (Option D)+1 ≤ N)
    (hsmall : ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))*
        ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option D) (Option D) (Option D) (Option D))+1)) :
    (∑ o : ∀ i,Frame (Coordinate k n b degree) H (Fin N) (E i),weights (PMF.uniformOfFintype _) o*
      ((∑ V : Matrix (Base k n) (Option D) Binary,
        conditionalLaw (weights (PMF.uniformOfFintype _)) (GramEvent sel E G) V*
          test (fun i => batchEquiv ((o i).P*pointColumns sel V,(o i).Q*pointColumns sel V)))-
            referenceMean N G test)^2) ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound N (Option D) (Option D) (Option D) (Option D)+
        4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2) := by
  classical
  let ρ := weights (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary))
  let C := GramEvent (D := D) sel E G
  let κ := conditionalLaw ρ C
  have hC : 0 < cellMass ρ C := hβ.trans_le hGram
  have hκ : Probability κ :=
    ⟨RetainedImages.conditional_law_nonneg ρ C (RealCellLaws.weights_nonneg _),
      RetainedImages.conditional_law_total ρ C hC⟩
  have hfixed : ∀ V,κ V ≠ 0 → ∀ i,(pointColumns sel V).transpose*E i*pointColumns sel V = G i := by
    intro V hV
    have hCV : C V := by
      by_contra hh
      apply hV
      simp [κ,conditionalLaw,hh]
    exact hCV
  have hbad := ConditionedAffineColumns.conditioned_nominal_pair_failure (degree := degree) sel C β hβ hGram
  have hmass : cellMass (fun ab : Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary =>
      κ ab.1*κ ab.2) (fun ab => ¬ Function.Injective (Matrix.fromCols (pointColumns (degree := degree) sel ab.1)
        (pointColumns sel ab.2)).mulVec) ≤ ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2 := by
    apply LE.le.trans (FiniteSampling.cell_mass_mono _ _ _ (fun ab => mul_nonneg (hκ.1 _) (hκ.1 _)) ?_) hbad
    intro ab hAB hpair
    exact hAB (concatenation_injective _ _ hpair)
  exact coefficient_variance (H := H) N E G (pointColumns sel) κ hκ hfixed test htest
    _ hmass hN hsmall

/--
---
conclusion: Lax342547.AffineSliceVariance.independent_free_pair_bound
---
-/
theorem independent_free_pair_bound {A B : Type} [Fintype A] [Fintype B]
    (α : A → ℝ) (β : B → ℝ) (hα : Probability α) (_hβ : Probability β)
    (bad : (A × B) × (A × B) → Prop) (δ : ℝ)
    (hbad : ∀ a : A × A,cellMass (fun z : B × B => β z.1*β z.2)
      (fun z => bad ((a.1,z.1),(a.2,z.2))) ≤ δ) :
    cellMass (fun z : (A × B) × (A × B) => (α z.1.1*β z.1.2)*(α z.2.1*β z.2.2)) bad ≤ δ := by
  classical
  have he : cellMass (fun z : (A × B) × (A × B) => (α z.1.1*β z.1.2)*(α z.2.1*β z.2.2)) bad =
      ∑ a : A × A,(α a.1*α a.2)*cellMass (fun z : B × B => β z.1*β z.2)
        (fun z => bad ((a.1,z.1),(a.2,z.2))) := by
    unfold cellMass
    simp only [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a' _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro b' _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ ∑ a : A × A,(α a.1*α a.2)*δ := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hbad a) (mul_nonneg (hα.1 _) (hα.1 _))
    _ = δ := by
      rw [← Finset.sum_mul]
      have ht : ∑ a : A × A,α a.1*α a.2 = 1 := by
        simp only [Fintype.sum_prod_type,← Finset.mul_sum,hα.2,mul_one]
      rw [ht,one_mul]

set_option backward.isDefEq.respectTransparency true in
/--
---
conclusion: Lax342547.AffineSliceVariance.flavored_slice_variance
---
-/
theorem flavored_slice_variance {S H D A : Type} [Fintype S] [DecidableEq S]
    [Fintype H] [Fintype D] [DecidableEq D] [Fintype A] {k n b degree : ℕ}
    (N : ℕ) (sel : Fin b → Binary)
    (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option D) (Option D) Binary)
    [∀ i,Nonempty (Frame (Coordinate k n b degree) H (Fin N) (E i))]
    [∀ i,Nonempty (Orbit (Fin N) (G i))]
    (μ : A → ℝ) (hμ : Probability μ) (V : A → Matrix (Base k n) (Option D) Binary)
    (β : ℝ) (hβ : 0 < β)
    (hGram : β ≤ cellMass (flavoredLaw (n := n) (D := D) μ) (fun a => GramEvent (k := k) (n := n) (b := b) (degree := degree) sel E G (setFree (k := k) (n := n) (D := D) (V a.1) a.2)))
    (test : (S → (Fin N × (Option D ⊕ Option D) → Binary)) → ℝ) (htest : ∀ z,|test z| ≤ 1)
    (hN : Fintype.card (Option D)+Fintype.card (Option D)+1 ≤ N)
    (hsmall : ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))*
        ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option D) (Option D) (Option D) (Option D))+1)) :
    (∑ o : ∀ i,Frame (Coordinate k n b degree) H (Fin N) (E i),weights (PMF.uniformOfFintype _) o*
      ((∑ a : A × Matrix (Fin n) (Option D) Binary,conditionedFlavorLaw sel E G μ V a*
          test (fun i => batchEquiv ((o i).P*pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V a.1) a.2),
            (o i).Q*pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V a.1) a.2))))-referenceMean N G test)^2) ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound N (Option D) (Option D) (Option D) (Option D)+
        4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2) := by
  classical
  let ρ := flavoredLaw (n := n) (D := D) μ
  let C := fun a : A × Matrix (Fin n) (Option D) Binary => GramEvent (k := k) (n := n) (b := b) (degree := degree) sel E G (setFree (k := k) (n := n) (D := D) (V a.1) a.2)
  let κ := conditionalLaw ρ C
  let freeWeights := weights (PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary))
  have hb : Probability freeWeights := ⟨RealCellLaws.weights_nonneg _,RealCellLaws.weights_total _⟩
  have hρ : Probability ρ := by
    refine ⟨fun a => mul_nonneg (hμ.1 _) (hb.1 _),?_⟩
    simp only [ρ,flavoredLaw,Fintype.sum_prod_type,← Finset.mul_sum,RealCellLaws.weights_total,mul_one,hμ.2]
  have hC : 0 < cellMass ρ C := hβ.trans_le hGram
  have hκ : Probability κ :=
    ⟨RetainedImages.conditional_law_nonneg ρ C hρ.1,RetainedImages.conditional_law_total ρ C hC⟩
  have hfixed : ∀ a,κ a ≠ 0 → ∀ i,
      (pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V a.1) a.2)).transpose*E i*pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V a.1) a.2) = G i := by
    intro a ha
    have hc : C a := by
      by_contra hh
      apply ha
      simp [κ,conditionalLaw,hh]
    exact hc
  let bad := fun ab : (A × Matrix (Fin n) (Option D) Binary) × (A × Matrix (Fin n) (Option D) Binary) =>
    ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
      (pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V ab.1.1) ab.1.2)).mulVec uv.1+
      (pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V ab.2.1) ab.2.2)).mulVec uv.2)
  have hlocal : ∀ a : A × A,cellMass (fun z : Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary => freeWeights z.1*freeWeights z.2)
      (fun z => bad ((a.1,z.1),(a.2,z.2))) ≤ (2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n := by
    intro a
    have hh := ENNReal.toReal_mono (by apply ENNReal.div_ne_top <;> simp :
        (2 : ENNReal)^(2*Fintype.card D+1)/(2 : ENNReal)^n ≠ ⊤)
      (AffineSliceIndependence.point_pair_failure (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (V a.1) (V a.2))
    rw [← RealCellLaws.event_mass] at hh
    simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hh
    have he : weights (PMF.uniformOfFintype
        (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary)) =
        (fun z => freeWeights z.1*freeWeights z.2) := funext ConditionedAffineColumns.uniform_pair_weights
    rw [he] at hh
    exact hh
  have hf := independent_free_pair_bound μ freeWeights hμ hb bad _ hlocal
  have hf' := ConditionedAffineColumns.conditioning_pair_bound ρ C bad β _ hρ.1 hβ hGram hf
  have hbad : cellMass (fun ab : (A × Matrix (Fin n) (Option D) Binary) × (A × Matrix (Fin n) (Option D) Binary) =>
      κ ab.1*κ ab.2) (fun ab => ¬ Function.Injective (Matrix.fromCols
        (pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V ab.1.1) ab.1.2))
        (pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V ab.2.1) ab.2.2))).mulVec) ≤
        ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2 := by
    apply LE.le.trans (FiniteSampling.cell_mass_mono _ _ bad (fun ab => mul_nonneg (hκ.1 _) (hκ.1 _)) ?_) hf'
    intro ab hab hpair
    exact hab (concatenation_injective _ _ hpair)
  exact coefficient_variance (S := S) (B := Coordinate k n b degree) (H := H) (D := Option D)
    (A := A × Matrix (Fin n) (Option D) Binary) N E G (fun a : A × Matrix (Fin n) (Option D) Binary => pointColumns (k := k) (n := n) (b := b) (degree := degree) (D := D) sel (setFree (k := k) (n := n) (D := D) (V a.1) a.2))
    κ hκ hfixed test htest _ hbad hN hsmall

end
end Lax342547Proofs.AffineSliceVariance
