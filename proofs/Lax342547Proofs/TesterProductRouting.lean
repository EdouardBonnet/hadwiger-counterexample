import Lax342547.TesterProductRouting
import Lax342547Proofs.FixedSelectorGram

namespace Lax342547Proofs.TesterProductRouting
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.Atoms
open Lax342547.FixedSelectorGram Lax342547.FlavorAffineSlices Lax342547.AffineSliceIndependence
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

open Lax342547.TesterProductRouting

/--
---
conclusion: Lax342547.TesterProductRouting.sum_extended_product
---
-/
theorem sum_extended_product {I J : Type} [Fintype I] [Fintype J]
    (c : I → J) (hc : Function.Injective c) (a b : I → Binary) :
    (∑ j,Function.extend c a 0 j*Function.extend c b 0 j) = ∑ i,a i*b i := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image c,Function.extend c a 0 j*Function.extend c b 0 j := by
      symm
      apply Finset.sum_subset (Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _))
      intro j _ hj
      have hn : ¬∃ i,c i = j := by simpa using hj
      rw [Function.extend_apply' a (0 : J → Binary) j hn]
      simp
    _ = ∑ i,Function.extend c a 0 (c i)*Function.extend c b 0 (c i) := by
      rw [Finset.sum_image]
      exact fun i _ j _ hh => hc hh
    _ = _ := by simp only [hc.extend_apply]

/--
---
conclusion: Lax342547.TesterProductRouting.routed_product_gram
---
-/
theorem routed_product_gram {k r : ℕ} {l : Tag k} {f : Flavor k} {D I : Type}
    [Fintype I] (c : I → Pairs l f r) (hc : Function.Injective c)
    (a b : I → Option D → Binary) :
    restrictedGram (productRouting c a b) = fun x y => ∑ i,a i x*b i y := by
  classical
  ext x y
  unfold restrictedGram
  rw [← Fintype.sum_prod_type (fun p : Pairs l f r => productRouting c a b (p.1,p.2,false) x*productRouting c a b (p.1,p.2,true) y)]
  simp only [productRouting,Bool.false_eq_true,↓reduceIte]
  exact sum_extended_product c hc _ _

/--
---
conclusion: Lax342547.TesterProductRouting.product_gram_cell_mass
---
-/
theorem product_gram_cell_mass {k n b degree r : ℕ} {D I : Type} [Fintype D] [Fintype I]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k) (c : I → Pairs l f r) (hc : Function.Injective c)
    (a b' : I → Option D → Binary) :
    massFloor l f r D ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l f D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
        fun x y => ∑ i,a i x*b' i y) := by
  classical
  have hh : 1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D)) ≤
      (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
      {V | (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
        fun x y => ∑ i,a i x*b' i y} := by
    rw [← FixedSelectorGram.prescription_mass hr l f (productRouting c a b')]
    apply (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure.mono
    intro V hV
    change restrictTesters hr l f V = productRouting c a b' at hV
    change (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = _
    rw [FixedSelectorGram.gram_restriction,hV,routed_product_gram c hc]
  have ht : (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
      {V | (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
        fun x y => ∑ i,a i x*b' i y} ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    apply ((PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure.mono (Set.subset_univ _)).trans_eq
    simpa [PMF.toOuterMeasure_apply] using (PMF.uniformOfFintype (Coefficients n l f D)).tsum_coe
  have ht' := ENNReal.toReal_mono ht hh
  rw [← RealCellLaws.event_mass] at ht'
  simpa only [massFloor,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using ht'

end
end Lax342547Proofs.TesterProductRouting
