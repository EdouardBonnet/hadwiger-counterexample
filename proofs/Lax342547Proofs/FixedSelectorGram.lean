import Lax342547.FixedSelectorGram
import Lax342547Proofs.FlavorAffineSlices

namespace Lax342547Proofs.FixedSelectorGram
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AffineSliceIndependence Lax342547.FlavorAffineSlices Lax342547.Atoms
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
open Lax342547.FixedSelectorGram

theorem gram_entry {B I J : Type} [Fintype B] [DecidableEq B]
    (E : Matrix B B Binary) (C : Matrix B I Binary) (D : Matrix B J Binary)
    (i : I) (j : J) :
    (C.transpose * E * D) i j = E.toBilin' (C.col i) (D.col j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.col_apply,
    Matrix.toBilin'_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sharp_columns_zero {k n b degree : ℕ} {D J : Type}
    (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s : Fin b → Binary) (V : Matrix (Base k n) (Option D) Binary)
    (W : Matrix (Base k n) (Option J) Binary) (i : Option D) (j : Option J) :
    sharpForm hd M ((pointColumns s V).col i) ((pointColumns s W).col j) = 0 := by
  rw [ConcreteGeometry.sharpForm_apply]
  simp only [Matrix.col_apply, pointColumns, ConcreteGeometry.eval_bit,
    ConcreteGeometry.eval_empty, one_mul]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  have he : (2 : Binary) = 0 := by decide
  ring_nf
  simp [he]

/--
---
conclusion: Lax342547.FixedSelectorGram.same_selector_gram
---
-/
theorem same_selector_gram {k n b degree r : ℕ} {D : Type}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (V W : Matrix (Base k n) (Option D) Binary) :
    (pointColumns s V).transpose*selfGram hr hd M*pointColumns s W =
      fun i j => (∑ d : Tag k,∑ t : Tag k,∑ ρ : Fin r,
        V (ordinary d t (pairLeft hr ρ)) i*W (ordinary d t (pairRight hr ρ)) j)+
        ∑ ρ : Fin r,V (shared (pairLeft hr ρ)) i*W (shared (pairRight hr ρ)) j := by
  classical
  ext i j
  rw [gram_entry]
  unfold Lax342547.ConcreteGeometry.selfGram
  rw [Matrix.toBilin'_toMatrix']
  simp only [LinearMap.add_apply,sharp_columns_zero,add_zero,testerForm,
    LinearMap.sum_apply,ConcreteGeometry.blockForm_apply,Matrix.col_apply,
    pointColumns,ConcreteGeometry.eval_empty,one_mul]

theorem testerCoordinate_injective {k n r : ℕ} (hr : 2*r ≤ n) :
    Function.Injective (testerCoordinate (k := k) hr) := by
  intro ⟨q,ρ,c⟩ ⟨p,σ,d⟩ hh
  have hi : Function.Injective (fun u : Fin r × Bool =>
      if u.2 then pairRight hr u.1 else pairLeft hr u.1) := by
    intro ⟨i,a⟩ ⟨j,b⟩ he
    cases a <;> cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at he
    all_goals have hv := congrArg Fin.val he
    all_goals simp [pairLeft,pairRight] at hv
    · exact Prod.ext (Fin.ext (by omega)) rfl
    · omega
    · omega
    · exact Prod.ext (Fin.ext (by omega)) rfl
  cases q with
  | none =>
    cases p with
    | none =>
      have he : (if c then pairRight hr ρ else pairLeft hr ρ) =
          (if d then pairRight hr σ else pairLeft hr σ) := by
        simpa [testerCoordinate,shared] using hh
      exact Prod.ext rfl (hi he)
    | some p => simp [testerCoordinate,shared,ordinary] at hh
  | some q =>
    cases p with
    | none => simp [testerCoordinate,shared,ordinary] at hh
    | some p =>
      have he : q = p ∧ (if c then pairRight hr ρ else pairLeft hr ρ) =
          (if d then pairRight hr σ else pairLeft hr σ) := by
        simpa [testerCoordinate,ordinary] using hh
      exact Prod.ext (congrArg some he.1) (hi he.2)

theorem tester_retained {k n r : ℕ} (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k)
    (q : TesterBlock k) (ρ : Fin r) (c : Bool) :
    testerCoordinate hr (q,ρ,c) ∈ retained (n := n) l f ↔ blockRetained l f q := by
  change retained l f (testerCoordinate hr (q,ρ,c)) ↔ _
  cases q with
  | none => cases f <;> simp [testerCoordinate,shared,retained,blockRetained]
  | some q => cases f <;> simp [testerCoordinate,ordinary,retained,blockRetained]

theorem slotIndex_injective {k n r : ℕ} (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k) :
    Function.Injective (slotIndex hr l f) := by
  intro u v hh
  have he := testerCoordinate_injective hr (congrArg Subtype.val hh)
  have hq : u.1 = v.1 := Subtype.ext (congrArg Prod.fst he)
  have hp : u.2 = v.2 := congrArg (fun z : TesterBlock k × Fin r × Bool => z.2) he
  exact Prod.ext hq hp

/--
---
conclusion: Lax342547.FixedSelectorGram.restriction_uniform
---
-/
theorem restriction_uniform {k n r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k) :
    (PMF.uniformOfFintype (Coefficients n l f D)).map (restrictTesters hr l f) =
      PMF.uniformOfFintype (Matrix (Slots l f r) (Option D) Binary) := by
  classical
  apply FiniteLinearLaw.uniform_image_of_surjective
  intro X
  refine ⟨fun a j => Function.extend (slotIndex hr l f) (fun u => X u j) 0 a,?_⟩
  funext u j
  simpa only [restrictTesters,LinearMap.coe_mk,AddHom.coe_mk] using
    ((slotIndex_injective hr l f).extend_apply (fun u => X u j) 0 u)

/--
---
conclusion: Lax342547.FixedSelectorGram.prescription_mass
---
-/
theorem prescription_mass {k n r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k)
    (X : Matrix (Slots l f r) (Option D) Binary) :
    (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
      {V | restrictTesters hr l f V = X} =
        1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D)) := by
  classical
  have hh := congrArg (fun p => p.toOuterMeasure {X}) (restriction_uniform (D := D) hr l f)
  rw [PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at hh
  have hc : Fintype.card (Matrix (Slots l f r) (Option D) Binary) =
      2^(Fintype.card (Slots l f r)*Fintype.card (Option D)) := by
    rw [← Nat.card_eq_fintype_card]
    simp [Matrix,Binary,ZMod.card,pow_mul,Nat.card_eq_fintype_card,Nat.mul_comm]
  have he : (⇑(restrictTesters hr l f) ⁻¹' {X}) = {V | restrictTesters hr l f V = X} := by
    ext V
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  rw [he,hc] at hh
  simpa only [Nat.cast_pow,Nat.cast_ofNat,one_div] using hh

/--
---
conclusion: Lax342547.FixedSelectorGram.gram_restriction
---
-/
theorem gram_restriction {k n b degree r : ℕ} {D : Type}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k) (V : Coefficients n l f D) :
    (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
      restrictedGram (restrictTesters hr l f V) := by
  classical
  ext i j
  rw [same_selector_gram]
  let h : TesterBlock k → Binary := fun q => ∑ ρ : Fin r,
    value V (testerCoordinate hr (q,ρ,false)) i*value V (testerCoordinate hr (q,ρ,true)) j
  have hall : (∑ d : Tag k,∑ t : Tag k,∑ ρ : Fin r,
        value V (ordinary d t (pairLeft hr ρ)) i*value V (ordinary d t (pairRight hr ρ)) j)+
        ∑ ρ : Fin r,value V (shared (pairLeft hr ρ)) i*value V (shared (pairRight hr ρ)) j = ∑ q,h q := by
    simp [h,Fintype.sum_option,Fintype.sum_prod_type,testerCoordinate,add_comm]
  change _ = ∑ q : {q : TesterBlock k // blockRetained l f q},∑ ρ : Fin r, _
  simp only []
  rw [hall,← Fintype.sum_subtype_add_sum_subtype (blockRetained l f) h]
  have hz : ∑ q : {q : TesterBlock k // ¬blockRetained l f q},h q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro ρ _
    have hn : testerCoordinate hr (q.val,ρ,false) ∉ retained (n := n) l f :=
      fun hh => q.property ((tester_retained hr l f _ _ _).mp hh)
    simp [value,parameterValue,hn]
  rw [hz,add_zero]
  apply Finset.sum_congr
  · ext q; simp
  intro q _
  apply Finset.sum_congr rfl
  intro ρ _
  have ha := (slotIndex hr l f (q,ρ,false)).property
  have hb := (slotIndex hr l f (q,ρ,true)).property
  change testerCoordinate hr (q.val,ρ,false) ∈ retained (n := n) l f at ha
  change testerCoordinate hr (q.val,ρ,true) ∈ retained (n := n) l f at hb
  simp only [value,parameterValue,dif_pos ha,dif_pos hb,
    restrictTesters,LinearMap.coe_mk,AddHom.coe_mk,slotIndex]

/--
---
conclusion: Lax342547.FixedSelectorGram.routed_gram
---
-/
theorem routed_gram {k r : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    [Fintype D]
    (c : Option D → Pairs l f r) (hc : Function.Injective c)
    (G : Matrix (Option D) (Option D) Binary) : restrictedGram (routing c G) = G := by
  classical
  ext i j
  unfold restrictedGram
  rw [← Fintype.sum_prod_type (fun p : Pairs l f r => routing c G (p.1,p.2,false) i*routing c G (p.1,p.2,true) j)]
  simp only [routing,Bool.false_eq_true,↓reduceIte,ite_mul,zero_mul,one_mul]
  rw [Finset.sum_eq_single (c i)]
  · simp only [ite_true]
    exact hc.extend_apply _ _ _
  · intro p _ hp
    simp [hp]
  · simp

/--
---
conclusion: Lax342547.FixedSelectorGram.gram_mass_bound
---
-/
theorem gram_mass_bound {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k)
    (c : Option D → Pairs l f r) (hc : Function.Injective c)
    (G : Matrix (Option D) (Option D) Binary) :
    1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D)) ≤
      (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
        {V | (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G} := by
  classical
  rw [← prescription_mass hr l f (routing c G)]
  apply (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure.mono
  intro V hV
  change restrictTesters hr l f V = routing c G at hV
  change (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G
  rw [gram_restriction, hV, routed_gram c hc]

/--
---
conclusion: Lax342547.FixedSelectorGram.positive_gram_mass
---
-/
theorem positive_gram_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k)
    (hroom : Fintype.card (Option D) ≤ Fintype.card (Pairs l f r))
    (G : Matrix (Option D) (Option D) Binary) :
    1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D)) ≤
      (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
        {V | (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G} := by
  classical
  let c : Option D → Pairs l f r := fun j =>
    (Fintype.equivFin (Pairs l f r)).symm (Fin.castLE hroom ((Fintype.equivFin (Option D)) j))
  have hc : Function.Injective c := (Fintype.equivFin (Pairs l f r)).symm.injective.comp
    ((Fin.castLE_injective hroom).comp (Fintype.equivFin (Option D)).injective)
  exact gram_mass_bound hr hd M s l f c hc G

/--
---
conclusion: Lax342547.FixedSelectorGram.massFloor_pos
---
-/
theorem massFloor_pos {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) (D : Type) [Fintype D] :
    0 < massFloor l f r D := by unfold massFloor; positivity

/--
---
conclusion: Lax342547.FixedSelectorGram.gram_cell_mass
---
-/
theorem gram_cell_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k)
    (hroom : Fintype.card (Option D) ≤ Fintype.card (Pairs l f r))
    (G : Matrix (Option D) (Option D) Binary) :
    massFloor l f r D ≤ Lax342547.RetainedImages.cellMass
      (Lax342547.RealCellLaws.weights (PMF.uniformOfFintype (Coefficients n l f D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G) := by
  classical
  let p := PMF.uniformOfFintype (Coefficients n l f D)
  let C := fun V : Coefficients n l f D =>
    (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G
  have ht : p.toOuterMeasure {V | C V} ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    apply (p.toOuterMeasure.mono (Set.subset_univ _)).trans_eq
    simpa [PMF.toOuterMeasure_apply] using p.tsum_coe
  have hh := ENNReal.toReal_mono ht (positive_gram_mass hr hd M s l f hroom G)
  rw [← RealCellLaws.event_mass] at hh
  simpa only [massFloor,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hh

end
end Lax342547Proofs.FixedSelectorGram
