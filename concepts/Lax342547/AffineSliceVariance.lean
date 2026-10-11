import Lax342547.ConditionedAffineColumns
import Lax342547.RawGroupedComparison
import Lax342547.EmpiricalVariance

/-!
---
title: Conditioned affine-slice variance under the actual raw law
type: definition and theorem
---
The actual one-batch orbit law and grouped two-batch comparison discharge the
finite empirical-variance hypotheses. The coefficient law may have arbitrary
other coordinates and an independent uniform free block. Conditioning on a
positive-mass prescribed Gram event retains its explicit squared mass cost.
-/

namespace Lax342547.AffineSliceVariance
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RawFrames
open Lax342547.RealCellLaws Lax342547.GramOrbitDensity Lax342547.RelativeEntropy
open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.AffineSliceIndependence
open Lax342547.RetainedImages
open scoped BigOperators

def referenceMean {S D : Type} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
    (n : ℕ) (G : S → Matrix D D Binary) [∀ s,Nonempty (Orbit (Fin n) (G s))]
    (test : (S → (Fin n × (D ⊕ D) → Binary)) → ℝ) : ℝ :=
    ∑ z : ∀ s,Orbit (Fin n) (G s),weights (PMF.uniformOfFintype _) z*
      test (fun s => batchEquiv (z s).val)

axiom reference_mean {S B H D : Type} [Fintype S] [DecidableEq S]
    [Fintype B] [Fintype H] [Fintype D] [DecidableEq D]
    (n : ℕ) (E : S → Matrix B B Binary) (G : S → Matrix D D Binary)
    [∀ s,Nonempty (Frame B H (Fin n) (E s))] [∀ s,Nonempty (Orbit (Fin n) (G s))]
    (C : Matrix B D Binary) (hC : Function.Injective C.mulVec)
    (hG : ∀ s,C.transpose*E s*C = G s)
    (test : (S → (Fin n × (D ⊕ D) → Binary)) → ℝ) :
    (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
      test (fun s => batchEquiv ((o s).P*C,(o s).Q*C))) =
    ∑ z : ∀ s,Orbit (Fin n) (G s),weights (PMF.uniformOfFintype _) z*
      test (fun s => batchEquiv (z s).val)

axiom coefficient_variance {S B H D A : Type} [Fintype S] [DecidableEq S]
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
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound n D D D D+4*δ

def GramEvent {S D : Type} {k n b degree : ℕ} [Fintype D]
    (sel : Fin b → Binary) (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option D) (Option D) Binary)
    (V : Matrix (Base k n) (Option D) Binary) : Prop :=
    ∀ i,(pointColumns sel V).transpose*E i*pointColumns sel V = G i

axiom affine_slice_variance {S H D : Type} [Fintype S] [DecidableEq S]
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
        4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2)

axiom independent_free_pair_bound {A B : Type} [Fintype A] [Fintype B]
    (α : A → ℝ) (β : B → ℝ) (hα : Probability α) (_hβ : Probability β)
    (bad : (A × B) × (A × B) → Prop) (δ : ℝ)
    (hbad : ∀ a : A × A,cellMass (fun z : B × B => β z.1*β z.2)
      (fun z => bad ((a.1,z.1),(a.2,z.2))) ≤ δ) :
    cellMass (fun z : (A × B) × (A × B) => (α z.1.1*β z.1.2)*(α z.2.1*β z.2.2)) bad ≤ δ

def flavoredLaw {A D : Type} [Fintype D] [DecidableEq D] {n : ℕ} (μ : A → ℝ) :
    (A × Matrix (Fin n) (Option D) Binary) → ℝ :=
    fun a => μ a.1*weights (PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary)) a.2

def conditionedFlavorLaw {S A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {k n b degree : ℕ} (sel : Fin b → Binary)
    (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option D) (Option D) Binary)
    (μ : A → ℝ) (V : A → Matrix (Base k n) (Option D) Binary) :
    (A × Matrix (Fin n) (Option D) Binary) → ℝ :=
    conditionalLaw (flavoredLaw μ) (fun a => GramEvent sel E G (setFree (V a.1) a.2))

axiom flavored_slice_variance {S H D A : Type} [Fintype S] [DecidableEq S]
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
        4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2)

end
end Lax342547.AffineSliceVariance
