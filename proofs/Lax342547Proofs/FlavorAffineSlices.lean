import Lax342547.FlavorAffineSlices
import Lax342547Proofs.AffineSliceVariance
import Lax342547Proofs.Atoms

namespace Lax342547Proofs.FlavorAffineSlices
noncomputable section
open Lax342547.FlavorAffineSlices
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AffineSliceIndependence Lax342547.RetainedImages Lax342547.RealCellLaws
open Lax342547.RawFrames Lax342547.FrameTuples Lax342547.GramOrbitDensity Lax342547.RelativeEntropy
open Lax342547.AffineSliceVariance
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false



 theorem value_free {k n : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (V : Coefficients n l f D) (i : Fin n) (j : Option D) :
    value V (free i) j = V (freeIndex l f i) j := by
  have hi : free i ∈ retained (n := n) l f := (freeIndex l f i).property
  simp only [value,parameterValue,dif_pos hi]
  rfl

 theorem freePair_value {k n : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (V : Coefficients n l f D × Coefficients n l f D) :
    freePairMap V = (freePart (value V.1),freePart (value V.2)) := by
  apply Prod.ext <;> funext i j <;> simp [freePairMap,freePart,value_free]

/--
---
conclusion: Lax342547.FlavorAffineSlices.free_pair_uniform
---
-/
theorem free_pair_uniform {k n : ℕ} (l : Tag k) (f : Flavor k) {D : Type}
    [Fintype D] [DecidableEq D] :
    (PMF.uniformOfFintype (Coefficients n l f D × Coefficients n l f D)).map freePairMap =
      PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary) := by
  classical
  apply FiniteLinearLaw.uniform_image_of_surjective
  intro Z
  let c (W : Matrix (Fin n) (Option D) Binary) : Coefficients n l f D :=
    fun a j => (setFree (k := k) (n := n) 0 W) a.val j
  refine ⟨(c Z.1,c Z.2),?_⟩
  apply Prod.ext <;> funext i j <;> simp [freePairMap,c,freeIndex,setFree,free]

/--
---
conclusion: Lax342547.FlavorAffineSlices.nominal_pair_failure
---
-/
theorem nominal_pair_failure {k n b degree : ℕ} (l : Tag k) (f : Flavor k)
    {D : Type} [Fintype D] [DecidableEq D] (s : Fin b → Binary) :
    (PMF.uniformOfFintype (Coefficients n l f D × Coefficients n l f D)).toOuterMeasure
      {V | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (value V.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (value V.2)).mulVec uv.2)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n := by
  classical
  let p := PMF.uniformOfFintype (Coefficients n l f D × Coefficients n l f D)
  have hu := congrArg (fun q => q.map joinedFree) (free_pair_uniform (n := n) (D := D) l f)
  rw [PMF.map_comp,AffineSliceIndependence.joinedFree_uniform] at hu
  have he : p.toOuterMeasure {V | ¬ Function.Injective (joinedFree (freePart (value V.1),freePart (value V.2))).mulVec} =
      (PMF.uniformOfFintype (Matrix (Fin n) (Option (D ⊕ D)) Binary)).toOuterMeasure
        {Z | ¬ Function.Injective Z.mulVec} := by
    have ht := congrArg (fun q => q.toOuterMeasure {Z | ¬ Function.Injective Z.mulVec}) hu
    rw [PMF.toOuterMeasure_map_apply] at ht
    change p.toOuterMeasure {V | ¬ Function.Injective (joinedFree (freePairMap V)).mulVec} = _ at ht
    simp_rw [freePair_value] at ht
    exact ht
  have hsub : {V : Coefficients n l f D × Coefficients n l f D |
      ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (value V.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (value V.2)).mulVec uv.2)} ⊆
      {V | ¬ Function.Injective (joinedFree (freePart (value V.1),freePart (value V.2))).mulVec} := by
    intro V hV hZ
    exact hV (AffineSliceIndependence.point_pair_independent s (value V.1) (value V.2) hZ)
  have hh := p.toOuterMeasure.mono hsub
  change p.toOuterMeasure {V | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
      (pointColumns (degree := degree) s (value V.1)).mulVec uv.1+
        (pointColumns (degree := degree) s (value V.2)).mulVec uv.2)} ≤
    p.toOuterMeasure {V | ¬ Function.Injective (joinedFree (freePart (value V.1),freePart (value V.2))).mulVec} at hh
  rw [he] at hh
  exact hh.trans (by simpa only [Fintype.card_option,Fintype.card_sum,Fintype.card_fin,two_mul,add_assoc,add_comm,add_left_comm]
    using (GramNormalization.column_failure (J := Option (D ⊕ D)) (N := Fin n)))

/--
---
conclusion: Lax342547.FlavorAffineSlices.conditioned_pair_failure
---
-/
theorem conditioned_pair_failure {k n b degree : ℕ} (l : Tag k) (f : Flavor k)
    {D : Type} [Fintype D] [DecidableEq D] (s : Fin b → Binary)
    (C : Coefficients n l f D → Prop) (β : ℝ) (hβ : 0 < β)
    (hC : β ≤ cellMass (weights (PMF.uniformOfFintype (Coefficients n l f D))) C) :
    cellMass (fun V : Coefficients n l f D × Coefficients n l f D =>
        conditionalLaw (weights (PMF.uniformOfFintype _)) C V.1*
          conditionalLaw (weights (PMF.uniformOfFintype _)) C V.2)
      (fun V => ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (value V.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (value V.2)).mulVec uv.2)) ≤
      ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2 := by
  classical
  have hf := ENNReal.toReal_mono (by apply ENNReal.div_ne_top <;> simp :
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n ≠ ⊤)
      (nominal_pair_failure (n := n) (degree := degree) (D := D) l f s)
  rw [← RealCellLaws.event_mass] at hf
  simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hf
  have he : weights (PMF.uniformOfFintype (Coefficients n l f D × Coefficients n l f D)) =
      (fun V => weights (PMF.uniformOfFintype (Coefficients n l f D)) V.1*
        weights (PMF.uniformOfFintype (Coefficients n l f D)) V.2) :=
    funext ConditionedAffineColumns.uniform_pair_weights
  rw [he] at hf
  exact ConditionedAffineColumns.conditioning_pair_bound _ C _ β _ (RealCellLaws.weights_nonneg _) hβ hC hf

/--
---
conclusion: Lax342547.FlavorAffineSlices.flavor_slice_variance
---
-/
theorem flavor_slice_variance {S H D : Type} [Fintype S] [DecidableEq S]
    [Fintype H] [Fintype D] [DecidableEq D] {k n b degree : ℕ}
    (l : Tag k) (f : Flavor k)
    (N : ℕ) (sel : Fin b → Binary)
    (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option D) (Option D) Binary)
    [∀ i,Nonempty (Frame (Coordinate k n b degree) H (Fin N) (E i))]
    [∀ i,Nonempty (Orbit (Fin N) (G i))]
    (β : ℝ) (hβ : 0 < β)
    (hGram : β ≤ cellMass (weights (PMF.uniformOfFintype (Coefficients n l f D)))
      (fun V : Coefficients n l f D => GramEvent sel E G (value V)))
    (test : (S → (Fin N × (Option D ⊕ Option D) → Binary)) → ℝ) (htest : ∀ z,|test z| ≤ 1)
    (hN : Fintype.card (Option D)+Fintype.card (Option D)+1 ≤ N)
    (hsmall : ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))*
        ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option D) (Option D) (Option D) (Option D))+1)) :
    (∑ o : ∀ i,Frame (Coordinate k n b degree) H (Fin N) (E i),weights (PMF.uniformOfFintype _) o*
      ((∑ V : Coefficients n l f D,
        conditionalLaw (weights (PMF.uniformOfFintype _)) (fun V : Coefficients n l f D => GramEvent sel E G (value V)) V*
          test (fun i => batchEquiv ((o i).P*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V),(o i).Q*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V))))-
            referenceMean N G test)^2) ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound N (Option D) (Option D) (Option D) (Option D)+
        4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2) := by
  classical
  let ρ := weights (PMF.uniformOfFintype (Coefficients n l f D))
  let C := fun V : Coefficients n l f D => GramEvent (D := D) sel E G (value V)
  let κ := conditionalLaw ρ C
  have hC : 0 < cellMass ρ C := hβ.trans_le hGram
  have hκ : Probability κ :=
    ⟨RetainedImages.conditional_law_nonneg ρ C (RealCellLaws.weights_nonneg _),
      RetainedImages.conditional_law_total ρ C hC⟩
  have hfixed : ∀ V,κ V ≠ 0 → ∀ i,(pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V)).transpose*E i*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V) = G i := by
    intro V hV
    have hCV : C V := by
      by_contra hh
      apply hV
      simp [κ,conditionalLaw,hh]
    exact hCV
  have hbad := conditioned_pair_failure (n := n) (degree := degree) (D := D) l f sel C β hβ hGram
  have hmass : cellMass (fun ab : Coefficients n l f D × Coefficients n l f D =>
      κ ab.1*κ ab.2) (fun ab => ¬ Function.Injective (Matrix.fromCols (pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value ab.1))
        (pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value ab.2))).mulVec) ≤ ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2 := by
    apply LE.le.trans (FiniteSampling.cell_mass_mono _ _ _ (fun ab => mul_nonneg (hκ.1 _) (hκ.1 _)) ?_) hbad
    intro ab hAB hpair
    exact hAB (AffineSliceVariance.concatenation_injective _ _ hpair)
  exact AffineSliceVariance.coefficient_variance (S := S) (B := Coordinate k n b degree)
    (H := H) (D := Option D) (A := Coefficients n l f D) N E G
    (fun V : Coefficients n l f D => pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V)) κ hκ hfixed test htest
    _ hmass hN hsmall

end
end Lax342547Proofs.FlavorAffineSlices
