import Lax342547.AffineSliceVariance
import Lax342547.Atoms

/-!
---
title: Affine-slice comparison for every actual atom flavor
type: definition and theorem
---
Lemma 9.4 uses independent uniform affine coefficients on exactly the actual
retained coordinates of the chosen flavor. The free projection is exactly
uniform for generic, shared-only and every pure flavor. Conditioning on all
prescribed component Grams has the explicit beta^-2 cost, with no cost for
setting excluded flavor coordinates to zero. Arbitrary bounded common tests
of the actual primal image arrays satisfy the checked variance budget.
-/

namespace Lax342547.FlavorAffineSlices
noncomputable section
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AffineSliceIndependence Lax342547.RetainedImages Lax342547.RealCellLaws
open Lax342547.RawFrames Lax342547.FrameTuples Lax342547.GramOrbitDensity Lax342547.RelativeEntropy
open Lax342547.AffineSliceVariance
open scoped BigOperators ENNReal

abbrev Coefficients {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) (D : Type) :=
    Matrix {i : Base k n // i ∈ retained (k := k) (n := n) l f} (Option D) Binary

 noncomputable instance {k n : ℕ} (l : Tag k) (f : Flavor k) (D : Type) [Fintype D] :
    Fintype (Coefficients n l f D) := Fintype.ofFinite _

noncomputable def value {k n : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (V : Coefficients n l f D) : Matrix (Base k n) (Option D) Binary :=
    fun i j => parameterValue (fun a => V a j) i

def freeIndex {k n : ℕ} (l : Tag k) (f : Flavor k) (i : Fin n) :
    {a : Base k n // a ∈ retained (k := k) (n := n) l f} :=
    ⟨free i,by
      cases f with
      | generic => trivial
      | sharedOnly => trivial
      | pure blocks => change (2 : Fin 3) ≠ 0; decide⟩

def freePairMap {k n : ℕ} {l : Tag k} {f : Flavor k} {D : Type} :
    (Coefficients n l f D × Coefficients n l f D) →ₗ[Binary]
      (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary) where
  toFun V := (fun i j => V.1 (freeIndex l f i) j,fun i j => V.2 (freeIndex l f i) j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

axiom free_pair_uniform {k n : ℕ} (l : Tag k) (f : Flavor k) {D : Type}
    [Fintype D] [DecidableEq D] :
    (PMF.uniformOfFintype (Coefficients n l f D × Coefficients n l f D)).map freePairMap =
      PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary)

axiom nominal_pair_failure {k n b degree : ℕ} (l : Tag k) (f : Flavor k)
    {D : Type} [Fintype D] [DecidableEq D] (s : Fin b → Binary) :
    (PMF.uniformOfFintype (Coefficients n l f D × Coefficients n l f D)).toOuterMeasure
      {V | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (value V.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (value V.2)).mulVec uv.2)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n

axiom conditioned_pair_failure {k n b degree : ℕ} (l : Tag k) (f : Flavor k)
    {D : Type} [Fintype D] [DecidableEq D] (s : Fin b → Binary)
    (C : Coefficients n l f D → Prop) (β : ℝ) (hβ : 0 < β)
    (hC : β ≤ cellMass (weights (PMF.uniformOfFintype (Coefficients n l f D))) C) :
    cellMass (fun V : Coefficients n l f D × Coefficients n l f D =>
        conditionalLaw (weights (PMF.uniformOfFintype _)) C V.1*
          conditionalLaw (weights (PMF.uniformOfFintype _)) C V.2)
      (fun V => ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (value V.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (value V.2)).mulVec uv.2)) ≤
      ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2

axiom flavor_slice_variance {S H D : Type} [Fintype S] [DecidableEq S]
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
        4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2)

end
end Lax342547.FlavorAffineSlices
