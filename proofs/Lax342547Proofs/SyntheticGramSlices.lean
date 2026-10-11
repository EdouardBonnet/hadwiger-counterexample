import Lax342547.SyntheticGramSlices
import Lax342547.FiniteSampling
import Lax342547.FlavorAffineSlices
import Lax342547.PureTesterRoom
import Lax342547.RealCellLaws
import Lax342547.TesterProductRouting

namespace Lax342547Proofs.SyntheticGramSlices
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.Atoms
open Lax342547.FixedSelectorGram Lax342547.FlavorAffineSlices Lax342547.AffineSliceIndependence
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RealCellLaws
open Lax342547.PureTesterRoom
open Lax342547.AffineSliceVariance Lax342547.RawFrames Lax342547.FrameTuples Lax342547.GramOrbitDensity
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

open Lax342547.SyntheticGramSlices

/--
---
conclusion: Lax342547.SyntheticGramSlices.slice_gram_products
---
-/
theorem slice_gram_products {q m : ℕ} (R C : Fin q → Fin m) :
    sliceGram R C = fun i j => ∑ p : Fin q,leftFactor q p i*rightFactor R C p j := by
  ext i j
  cases i with
  | none => simp [sliceGram,leftFactor]
  | some i =>
    cases i with
    | inr i => simp [sliceGram,leftFactor]
    | inl i =>
      cases j with
      | none => simp [sliceGram,rightFactor]
      | some j =>
        cases j with
        | inl j => simp [sliceGram,rightFactor]
        | inr j =>
          simp only [sliceGram,leftFactor,rightFactor]
          rw [Finset.sum_eq_single i]
          · simp
          · intro p _ hp
            simp [hp]
          · simp

/--
---
conclusion: Lax342547.SyntheticGramSlices.pure_slice_gram_mass
---
-/
theorem pure_slice_gram_mass {k n b degree r q m : ℕ}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (sel : Fin b → Binary)
    (l : Tag k) (T₀ : Finset (Tag k))
    (hroom : q ≤ k*(2*k+1-T₀.card)*r) (R C : Fin q → Fin m) :
    uniformFloor k r (Fin q ⊕ Fin q) ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q))))
      (fun V => (pointColumns sel (value V)).transpose*selfGram hr hd M*pointColumns sel (value V) = sliceGram R C) := by
  classical
  apply (Lax342547.PureTesterRoom.uniform_floor_bound l T₀ (Fin q ⊕ Fin q)).trans
  have hq : q ≤ Fintype.card (Pairs l (pureOutside T₀) r) := by
    rw [Lax342547.PureTesterRoom.pure_pairs_card]
    exact hroom
  let c : Fin q → Pairs l (pureOutside T₀) r := fun j =>
    (Fintype.equivFin (Pairs l (pureOutside T₀) r)).symm (Fin.castLE hq j)
  have hc : Function.Injective c := (Fintype.equivFin (Pairs l (pureOutside T₀) r)).symm.injective.comp
    (Fin.castLE_injective hq)
  have hh := Lax342547.TesterProductRouting.product_gram_cell_mass hr hd M sel l (pureOutside T₀)
    c hc (leftFactor q) (rightFactor R C)
  rw [← Lax342547.SyntheticGramSlices.slice_gram_products R C] at hh
  exact hh


/--
---
conclusion: Lax342547.SyntheticGramSlices.pure_slice_variance
---
-/
theorem pure_slice_variance {S H : Type} [Fintype S] [DecidableEq S]
    [Fintype H] {k n b degree r q m : ℕ}
    (l : Tag k) (T₀ : Finset (Tag k))
    (N : ℕ) (sel : Fin b → Binary)
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (R C : Fin q → Fin m)
    (hroom : q ≤ k*(2*k+1-T₀.card)*r)
    (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) Binary)
    [∀ i,Nonempty (Frame (Coordinate k n b degree) H (Fin N) (E i))]
    [∀ i,Nonempty (Orbit (Fin N) (G i))]
    (hE : ∀ i,E i = selfGram hr hd M) (hG : ∀ i,G i = sliceGram R C)
    (test : (S → (Fin N × (Option (Fin q ⊕ Fin q) ⊕ Option (Fin q ⊕ Fin q)) → Binary)) → ℝ) (htest : ∀ z,|test z| ≤ 1)
    (hN : Fintype.card (Option (Fin q ⊕ Fin q))+Fintype.card (Option (Fin q ⊕ Fin q))+1 ≤ N)
    (hsmall : ((2 : ℝ)^(Fintype.card (Option (Fin q ⊕ Fin q))*Fintype.card (Option (Fin q ⊕ Fin q))+2))*
        ((2 : ℝ)^(Fintype.card (Option (Fin q ⊕ Fin q))*Fintype.card (Option (Fin q ⊕ Fin q))+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)))+1)) :
    (∑ o : ∀ i,Frame (Coordinate k n b degree) H (Fin N) (E i),weights (PMF.uniformOfFintype _) o*
      ((∑ V : Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q),
        conditionalLaw (weights (PMF.uniformOfFintype _)) (fun V : Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q) => GramEvent sel E G (value V)) V*
          test (fun i => batchEquiv ((o i).P*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V),(o i).Q*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V))))-
            referenceMean N G test)^2) ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound N (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q))+
        4*(((2 : ℝ)^(2*Fintype.card (Fin q ⊕ Fin q)+1)/(2 : ℝ)^n)/(uniformFloor k r (Fin q ⊕ Fin q))^2)
 := by
  classical
  have hGram : uniformFloor k r (Fin q ⊕ Fin q) ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q))))
      (fun V => Lax342547.AffineSliceVariance.GramEvent sel E G (value V)) := by
    apply (Lax342547.SyntheticGramSlices.pure_slice_gram_mass hr hd M sel l T₀ hroom R C).trans
    apply Lax342547.FiniteSampling.cell_mass_mono _ _ _ (Lax342547.RealCellLaws.weights_nonneg _)
    intro V hV i
    rw [hE i,hG i]
    exact hV
  exact Lax342547.FlavorAffineSlices.flavor_slice_variance (S := S) (H := H) (D := Fin q ⊕ Fin q)
    l (pureOutside T₀) N sel E G (uniformFloor k r (Fin q ⊕ Fin q))
    (Lax342547.PureTesterRoom.uniformFloor_pos k r _) hGram test htest hN hsmall


end
end Lax342547Proofs.SyntheticGramSlices
