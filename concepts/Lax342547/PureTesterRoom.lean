import Lax342547.FixedSelectorGram

/-!
---
title: Exact pure-flavor tester room and a law-uniform Gram mass floor
type: lemma
---
The paper's pure flavor retains exactly k*(2k+1-|T0|)*r tester pairs.
Prescribing their affine coefficients gives a positive Gram mass floor
uniform over tags and excluded sets and independent of the free dimension.
-/

namespace Lax342547.PureTesterRoom
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.Atoms
open Lax342547.FixedSelectorGram Lax342547.FlavorAffineSlices Lax342547.AffineSliceIndependence
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false


def pureOutside {k : ℕ} (T₀ : Finset (Tag k)) : Flavor k := by
  classical
  exact .pure (Finset.univ.filter (fun p : Tag k × Tag k => p.2 ∉ T₀))

def retainedBlocksEquiv {k : ℕ} (l : Tag k) (T₀ : Finset (Tag k)) :
    {q : TesterBlock k // blockRetained l (pureOutside T₀) q} ≃
      ({d : Tag k // l ∈ interval k d} × {t : Tag k // t ∉ T₀}) where
  toFun q := by
    rcases q with ⟨q,hq⟩
    cases q with
    | none => simp [blockRetained,pureOutside] at hq
    | some q =>
      have hh : l ∈ interval k q.1 ∧ q.2 ∉ T₀ := by simpa [blockRetained,pureOutside] using hq
      exact (⟨q.1,hh.1⟩,⟨q.2,hh.2⟩)
  invFun p := ⟨some (p.1.val,p.2.val),by simpa [blockRetained,pureOutside] using And.intro p.1.property p.2.property⟩
  left_inv q := by
    rcases q with ⟨q,hq⟩
    cases q with
    | none => simp [blockRetained,pureOutside] at hq
    | some q => rfl
  right_inv p := by rfl

def uniformFloor (k r : ℕ) (D : Type) [Fintype D] : ℝ :=
  1/(2 : ℝ)^(2*k*(2*k+1)*r*Fintype.card (Option D))

axiom allowed_drivers_card (k : ℕ) (l : Tag k) :
    by classical exact Fintype.card {d : Tag k // l ∈ interval k d} = k

axiom pure_pairs_card {k r : ℕ} (l : Tag k) (T₀ : Finset (Tag k)) :
    Fintype.card (Pairs l (pureOutside T₀) r) = k*(2*k+1-T₀.card)*r

axiom pure_gram_cell_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (T₀ : Finset (Tag k))
    (hroom : Fintype.card (Option D) ≤ k*(2*k+1-T₀.card)*r)
    (G : Matrix (Option D) (Option D) Binary) :
    massFloor l (pureOutside T₀) r D ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G)

axiom slots_card {k r : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype.card (Slots l f r) = 2*Fintype.card (Pairs l f r)

axiom uniformFloor_pos (k r : ℕ) (D : Type) [Fintype D] :
    0 < uniformFloor k r D

axiom uniform_floor_bound {k r : ℕ} (l : Tag k) (T₀ : Finset (Tag k))
    (D : Type) [Fintype D] : uniformFloor k r D ≤ massFloor l (pureOutside T₀) r D

axiom uniform_pure_gram_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (T₀ : Finset (Tag k))
    (hroom : Fintype.card (Option D) ≤ k*(2*k+1-T₀.card)*r)
    (G : Matrix (Option D) (Option D) Binary) :
    uniformFloor k r D ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G)

end
end Lax342547.PureTesterRoom
