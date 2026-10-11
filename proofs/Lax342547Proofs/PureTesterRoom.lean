import Lax342547.PureTesterRoom
import Lax342547.FixedSelectorGram

namespace Lax342547Proofs.PureTesterRoom
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.Atoms
open Lax342547.FixedSelectorGram Lax342547.FlavorAffineSlices Lax342547.AffineSliceIndependence
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

open Lax342547.PureTesterRoom

/--
---
conclusion: Lax342547.PureTesterRoom.allowed_drivers_card
---
-/
theorem allowed_drivers_card (k : ℕ) (l : Tag k) :
    by classical exact Fintype.card {d : Tag k // l ∈ interval k d} = k := by
  classical
  let f : Fin k → Tag k := fun i => l-(i.val+1 : ℕ)
  have hf : Function.Injective f := by
    intro i j hh
    have he : (i.val+1 : ℕ) = j.val+1 := by
      have ht : ((i.val+1 : ℕ) : Tag k) = ((j.val+1 : ℕ) : Tag k) := sub_right_injective hh
      have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp ht
      rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hm
      exact hm
    exact Fin.ext (by omega)
  have hset : Finset.univ.filter (fun d : Tag k => l ∈ interval k d) = Finset.univ.image f := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,interval,Finset.mem_image]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨i,?_⟩
      dsimp [f]
      rw [← hi]
      simp
    · rintro ⟨i,hi⟩
      refine ⟨i,?_⟩
      rw [← hi]
      dsimp [f]
      simp
  rw [Fintype.card_subtype,hset,Finset.card_image_of_injective _ hf]
  simp

/--
---
conclusion: Lax342547.PureTesterRoom.pure_pairs_card
---
-/
theorem pure_pairs_card {k r : ℕ} (l : Tag k) (T₀ : Finset (Tag k)) :
    Fintype.card (Pairs l (pureOutside T₀) r) = k*(2*k+1-T₀.card)*r := by
  classical
  have hb : Fintype.card {q : TesterBlock k // blockRetained l (pureOutside T₀) q} =
      k*(2*k+1-T₀.card) := by
    rw [Fintype.card_congr (retainedBlocksEquiv l T₀),Fintype.card_prod,Lax342547.PureTesterRoom.allowed_drivers_card]
    congr 1
    rw [Fintype.card_subtype]
    have he : Finset.univ.filter (fun t : Tag k => t ∉ T₀) = T₀ᶜ := by ext t; simp
    rw [he,Finset.card_compl]
    simp [Tag,ZMod.card]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ({q : TesterBlock k // blockRetained l (pureOutside T₀) q} × Fin r) = _
  rw [Nat.card_prod]
  simp [Nat.card_eq_fintype_card,hb]

/--
---
conclusion: Lax342547.PureTesterRoom.pure_gram_cell_mass
---
-/
theorem pure_gram_cell_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (T₀ : Finset (Tag k))
    (hroom : Fintype.card (Option D) ≤ k*(2*k+1-T₀.card)*r)
    (G : Matrix (Option D) (Option D) Binary) :
    massFloor l (pureOutside T₀) r D ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G) := by
  apply Lax342547.FixedSelectorGram.gram_cell_mass hr hd M s l (pureOutside T₀) _ G
  simpa only [Lax342547.PureTesterRoom.pure_pairs_card] using hroom

/--
---
conclusion: Lax342547.PureTesterRoom.slots_card
---
-/
theorem slots_card {k r : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype.card (Slots l f r) = 2*Fintype.card (Pairs l f r) := by
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
  change Nat.card ({q : TesterBlock k // blockRetained l f q} × Fin r × Bool) =
    2*Nat.card ({q : TesterBlock k // blockRetained l f q} × Fin r)
  have hbool : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  simp only [Nat.card_prod,Nat.card_fin,hbool]
  ring

/--
---
conclusion: Lax342547.PureTesterRoom.uniformFloor_pos
---
-/
theorem uniformFloor_pos (k r : ℕ) (D : Type) [Fintype D] :
    0 < uniformFloor k r D := by unfold uniformFloor; positivity

/--
---
conclusion: Lax342547.PureTesterRoom.uniform_floor_bound
---
-/
theorem uniform_floor_bound {k r : ℕ} (l : Tag k) (T₀ : Finset (Tag k))
    (D : Type) [Fintype D] : uniformFloor k r D ≤ massFloor l (pureOutside T₀) r D := by
  unfold uniformFloor massFloor
  rw [Lax342547.PureTesterRoom.slots_card,Lax342547.PureTesterRoom.pure_pairs_card]
  have he : (2*(k*(2*k+1-T₀.card)*r))*Fintype.card (Option D) ≤
      2*k*(2*k+1)*r*Fintype.card (Option D) := by
    calc
      _ = 2*k*(2*k+1-T₀.card)*r*Fintype.card (Option D) := by ring
      _ ≤ _ := by gcongr; exact Nat.sub_le _ _
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he)

/--
---
conclusion: Lax342547.PureTesterRoom.uniform_pure_gram_mass
---
-/
theorem uniform_pure_gram_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (T₀ : Finset (Tag k))
    (hroom : Fintype.card (Option D) ≤ k*(2*k+1-T₀.card)*r)
    (G : Matrix (Option D) (Option D) Binary) :
    uniformFloor k r D ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G) :=
  (Lax342547.PureTesterRoom.uniform_floor_bound l T₀ D).trans (Lax342547.PureTesterRoom.pure_gram_cell_mass hr hd M s l T₀ hroom G)

end
end Lax342547Proofs.PureTesterRoom
