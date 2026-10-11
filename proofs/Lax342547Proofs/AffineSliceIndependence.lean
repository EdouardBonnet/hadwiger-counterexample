import Lax342547.AffineSliceIndependence
import Lax342547Proofs.GramNormalization
import Lax342547Proofs.FiniteLinearLaw
import Lax342547Proofs.ConcreteGeometry

namespace Lax342547Proofs.AffineSliceIndependence

open Lax342547.MomentSpace Lax342547.AffineSliceIndependence
open Lax342547.TagGeometry Lax342547.ConcreteGeometry
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

theorem joinedFree_surjective {D N : Type} : Function.Surjective (joinedFreeMap (D := D) (N := N)) := by
  intro M
  refine ⟨((fun n j => match j with
    | none => M n none
    | some d => M n (some (Sum.inl d))),
    (fun n j => match j with
    | none => 0
    | some d => M n (some (Sum.inr d)))),?_⟩
  ext n j
  cases j with
  | some j => cases j <;> rfl
  | none => exact add_zero _

/--
---
conclusion: Lax342547.AffineSliceIndependence.pairMap_injective_of_joined
---
-/
theorem pairMap_injective_of_joined {D N : Type} [Fintype D] [Fintype N]
    (Z : Matrix N (Option D) Binary × Matrix N (Option D) Binary)
    (hZ : Function.Injective (joinedFree Z).mulVec) : Function.Injective (pairMap Z) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨u,v⟩ huv
  have hn := congrFun huv none
  have hnone : u none+v none = 0 := by
    simpa [pairMap,affineColumns,Matrix.mulVec,dotProduct,Fintype.sum_option] using hn
  have huv0 : u none = v none := by
    have hself : v none+v none = 0 := ZModModule.add_self _
    exact add_right_cancel (hnone.trans hself.symm)
  let c : Option (D ⊕ D) → Binary
    | none => u none
    | some (Sum.inl d) => u (some d)
    | some (Sum.inr d) => v (some d)
  have hc : (joinedFree Z).mulVec c = 0 := by
    funext n
    have hh := congrFun huv (some n)
    change (∑ j,(joinedFree Z) n j*c j) = 0
    simp only [Fintype.sum_option,Fintype.sum_sum_type,c,joinedFree]
    have he : (Z.1 n none*u none+∑ d,Z.1 n (some d)*u (some d))+
        (Z.2 n none*v none+∑ d,Z.2 n (some d)*v (some d)) = 0 := by
      simpa [pairMap,affineColumns,Matrix.mulVec,dotProduct,Fintype.sum_option] using hh
    rw [← huv0] at he
    linear_combination he
  have hc0 : c = 0 := hZ (hc.trans (Matrix.mulVec_zero _).symm)
  apply Prod.ext
  · funext j
    cases j with
    | none => exact congrFun hc0 none
    | some d => exact congrFun hc0 (some (Sum.inl d))
  · funext j
    cases j with
    | none => exact huv0.symm.trans (congrFun hc0 none)
    | some d => exact congrFun hc0 (some (Sum.inr d))

/--
---
conclusion: Lax342547.AffineSliceIndependence.joinedFree_uniform
---
-/
theorem joinedFree_uniform {D N : Type} [Fintype D] [Fintype N] [DecidableEq D] [DecidableEq N] :
    (PMF.uniformOfFintype (Matrix N (Option D) Binary × Matrix N (Option D) Binary)).map joinedFree =
      PMF.uniformOfFintype (Matrix N (Option (D ⊕ D)) Binary) :=
  Lax342547Proofs.FiniteLinearLaw.uniform_image_of_surjective joinedFreeMap joinedFree_surjective

/--
---
conclusion: Lax342547.AffineSliceIndependence.affine_pair_failure
---
-/
theorem affine_pair_failure {D N : Type} [Fintype D] [Fintype N] [DecidableEq D] [DecidableEq N] :
    (PMF.uniformOfFintype (Matrix N (Option D) Binary × Matrix N (Option D) Binary)).toOuterMeasure
      {Z | ¬ Function.Injective (pairMap Z)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^Fintype.card N := by
  classical
  have hh := Lax342547Proofs.GramNormalization.column_failure (J := Option (D ⊕ D)) (N := N)
  rw [← joinedFree_uniform,PMF.toOuterMeasure_map_apply] at hh
  have hsub : {Z : Matrix N (Option D) Binary × Matrix N (Option D) Binary |
      ¬ Function.Injective (pairMap Z)} ⊆ {Z | ¬ Function.Injective (joinedFree Z).mulVec} :=
    fun Z hbad hgood => hbad (pairMap_injective_of_joined Z hgood)
  exact ((PMF.uniformOfFintype _).toOuterMeasure.mono hsub).trans
    (by simpa [Fintype.card_option,Fintype.card_sum,two_mul,add_comm] using hh)

/--
---
conclusion: Lax342547.AffineSliceIndependence.point_pair_independent
---
-/
theorem point_pair_independent {k n b degree : ℕ} {D : Type} [Fintype D]
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary)
    (hZ : Function.Injective (joinedFree (freePart V,freePart W)).mulVec) :
    Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
      (pointColumns (degree := degree) s V).mulVec uv.1+
        (pointColumns (degree := degree) s W).mulVec uv.2) := by
  have hfree := pairMap_injective_of_joined (freePart V,freePart W) hZ
  intro uv uv' he
  apply hfree
  ext j
  cases j with
  | none =>
    have hh := congrFun he (emptySelector b degree,none)
    simpa [pairMap,affineColumns,pointColumns,Matrix.mulVec,dotProduct,Fintype.sum_option] using hh
  | some i =>
    have hh := congrFun he (emptySelector b degree,some (free i))
    simpa [pairMap,affineColumns,pointColumns,freePart,Matrix.mulVec,dotProduct] using hh

/--
---
conclusion: Lax342547.AffineSliceIndependence.pointColumns_eraseFree
---
-/
theorem pointColumns_eraseFree {k n b degree : ℕ} {D : Type} [Fintype D]
    (s : Fin b → Binary) (V : Matrix (Base k n) (Option D) Binary) :
    (changeZ (0 : Matrix (Fin n) (Fin n) Binary)).toMatrix' * pointColumns (degree := degree) s V =
      pointColumns s (eraseFree V) := by
  ext c j
  change ((changeZ (0 : Matrix (Fin n) (Fin n) Binary)).toMatrix'.mulVec
    (fun c => pointColumns (degree := degree) s V c j)) c = _
  rw [LinearMap.toMatrix'_mulVec]
  rcases c with ⟨S,a⟩
  cases a with
  | none => rfl
  | some a =>
    cases a with
    | inl a => rfl
    | inr a =>
      rcases a with ⟨q,i⟩
      by_cases hq : q = 2 <;> simp [changeZ,pointColumns,eraseFree,hq]

/--
---
conclusion: Lax342547.AffineSliceIndependence.point_gram_ignores_free
---
-/
theorem point_gram_ignores_free {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary) :
    (pointColumns s V).transpose*selfGram hr hd M*pointColumns s W =
      (pointColumns s (eraseFree V)).transpose*selfGram hr hd M*pointColumns s (eraseFree W) := by
  have hE := Lax342547Proofs.ConcreteGeometry.selfGram_changeZ (k := k) hr hd M
    (0 : Matrix (Fin n) (Fin n) Binary)
  let Z := (changeZ (k := k) (b := b) (degree := degree) (0 : Matrix (Fin n) (Fin n) Binary)).toMatrix'
  have hV := pointColumns_eraseFree (degree := degree) s V
  have hW := pointColumns_eraseFree (degree := degree) s W
  change Z*pointColumns (degree := degree) s V = _ at hV
  change Z*pointColumns (degree := degree) s W = _ at hW
  calc
    _ = (pointColumns (degree := degree) s V).transpose*
        (Z.transpose*selfGram (k := k) hr hd M*Z)*pointColumns (degree := degree) s W := by rw [hE]
    _ = (Z*pointColumns (degree := degree) s V).transpose*selfGram (k := k) hr hd M*
        (Z*pointColumns (degree := degree) s W) := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hV,hW]

@[simp] theorem freePart_setFree {k n : ℕ} {D : Type}
    (V : Matrix (Base k n) (Option D) Binary) (Z : Matrix (Fin n) (Option D) Binary) :
    freePart (setFree V Z) = Z := by ext i j; simp [freePart,setFree,free]

@[simp] theorem eraseFree_setFree {k n : ℕ} {D : Type}
    (V : Matrix (Base k n) (Option D) Binary) (Z : Matrix (Fin n) (Option D) Binary) :
    eraseFree (setFree V Z) = eraseFree V := by
  ext a j
  cases a with
  | inl a => rfl
  | inr a =>
    rcases a with ⟨q,i⟩
    by_cases hq : q = 2 <;> simp [eraseFree,setFree,hq]

/--
---
conclusion: Lax342547.AffineSliceIndependence.point_gram_setFree
---
-/
theorem point_gram_setFree {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary)
    (Z T : Matrix (Fin n) (Option D) Binary) :
    (pointColumns s (setFree V Z)).transpose*selfGram hr hd M*pointColumns s (setFree W T) =
      (pointColumns s V).transpose*selfGram hr hd M*pointColumns s W := by
  rw [point_gram_ignores_free,eraseFree_setFree,eraseFree_setFree]
  exact (point_gram_ignores_free hr hd M s V W).symm

/--
---
conclusion: Lax342547.AffineSliceIndependence.point_pair_failure
---
-/
theorem point_pair_failure {k n b degree : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary)).toOuterMeasure
      {Z | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (setFree V Z.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (setFree W Z.2)).mulVec uv.2)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n := by
  classical
  have hsub : {Z : Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary |
      ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (setFree V Z.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (setFree W Z.2)).mulVec uv.2)} ⊆
      {Z | ¬ Function.Injective (joinedFree Z).mulVec} := by
    intro Z hbad hgood
    apply hbad
    exact point_pair_independent s _ _ (by simpa using hgood)
  have hh := Lax342547Proofs.GramNormalization.column_failure (J := Option (D ⊕ D)) (N := Fin n)
  rw [← joinedFree_uniform,PMF.toOuterMeasure_map_apply] at hh
  exact ((PMF.uniformOfFintype _).toOuterMeasure.mono hsub).trans
    (by simpa [Fintype.card_option,Fintype.card_sum,two_mul,add_comm] using hh)

end Lax342547Proofs.AffineSliceIndependence
