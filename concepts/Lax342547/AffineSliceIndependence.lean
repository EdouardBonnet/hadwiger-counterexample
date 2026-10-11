import Lax342547.GramNormalization
import Lax342547.ConcreteGeometry

/-!
---
title: Independent nominal affine slices from the free block
type: lemma
---
Two affine maps have the same constant-coordinate value on their translation
columns. Subtracting those columns leaves an independent uniform free matrix
with 2d+1 columns. This pays nominal dependence without falsely identifying
the two translation directions.
-/

namespace Lax342547.AffineSliceIndependence

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open scoped ENNReal

def affineColumns {D N : Type} (Z : Matrix N (Option D) Binary) :
    Matrix (Option N) (Option D) Binary
  | none,none => 1
  | none,some _ => 0
  | some n,j => Z n j

def joinedFree {D N : Type} (Z : Matrix N (Option D) Binary × Matrix N (Option D) Binary) :
    Matrix N (Option (D ⊕ D)) Binary
  | n,none => Z.1 n none+Z.2 n none
  | n,some (Sum.inl d) => Z.1 n (some d)
  | n,some (Sum.inr d) => Z.2 n (some d)

def joinedFreeMap {D N : Type} :
    (Matrix N (Option D) Binary × Matrix N (Option D) Binary) →ₗ[Binary]
      Matrix N (Option (D ⊕ D)) Binary where
  toFun := joinedFree
  map_add' Z W := by
    ext n j
    cases j with
    | some j => cases j <;> rfl
    | none => change (Z.1 n none+W.1 n none)+(Z.2 n none+W.2 n none) =
                (Z.1 n none+Z.2 n none)+(W.1 n none+W.2 n none)
              ring
  map_smul' c Z := by
    ext n j
    cases j with
    | some j => cases j <;> rfl
    | none => change c*(Z.1 n none)+c*(Z.2 n none) = c*(Z.1 n none+Z.2 n none)
              ring

def pairMap {D N : Type} [Fintype D] (Z : Matrix N (Option D) Binary × Matrix N (Option D) Binary) :
    ((Option D → Binary) × (Option D → Binary)) →ₗ[Binary] (Option N → Binary) where
  toFun v := (affineColumns Z.1).mulVec v.1+(affineColumns Z.2).mulVec v.2
  map_add' _ _ := by simp only [Prod.fst_add,Prod.snd_add,Matrix.mulVec_add]; abel
  map_smul' c v := by
    change (affineColumns Z.1).mulVec (c • v.1)+(affineColumns Z.2).mulVec (c • v.2) = _
    simp [Matrix.mulVec_smul,smul_add]

axiom pairMap_injective_of_joined {D N : Type} [Fintype D] [Fintype N]
    (Z : Matrix N (Option D) Binary × Matrix N (Option D) Binary)
    (hZ : Function.Injective (joinedFree Z).mulVec) : Function.Injective (pairMap Z)

axiom joinedFree_uniform {D N : Type} [Fintype D] [Fintype N] [DecidableEq D] [DecidableEq N] :
    (PMF.uniformOfFintype (Matrix N (Option D) Binary × Matrix N (Option D) Binary)).map joinedFree =
      PMF.uniformOfFintype (Matrix N (Option (D ⊕ D)) Binary)

axiom affine_pair_failure {D N : Type} [Fintype D] [Fintype N] [DecidableEq D] [DecidableEq N] :
    (PMF.uniformOfFintype (Matrix N (Option D) Binary × Matrix N (Option D) Binary)).toOuterMeasure
      {Z | ¬ Function.Injective (pairMap Z)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^Fintype.card N

/-- Coefficients of the actual affine point map at a fixed selector. -/
def pointColumns {k n b degree : ℕ} {D : Type} (s : Fin b → Binary)
    (V : Matrix (Base k n) (Option D) Binary) : Matrix (Coordinate k n b degree) (Option D) Binary :=
  fun c j => selectorEval s c.1 * match c.2 with
    | none => match j with | none => 1 | some _ => 0
    | some a => V a j

def freePart {k n : ℕ} {D : Type} (V : Matrix (Base k n) (Option D) Binary) :
    Matrix (Fin n) (Option D) Binary := fun i j => V (free i) j

def eraseFree {k n : ℕ} {D : Type} (V : Matrix (Base k n) (Option D) Binary) :
    Matrix (Base k n) (Option D) Binary
  | Sum.inr (q,i),j => if q = 2 then 0 else V (Sum.inr (q,i)) j
  | Sum.inl a,j => V (Sum.inl a) j

def setFree {k n : ℕ} {D : Type} (V : Matrix (Base k n) (Option D) Binary)
    (Z : Matrix (Fin n) (Option D) Binary) : Matrix (Base k n) (Option D) Binary
  | Sum.inr (q,i),j => if q = 2 then Z i j else V (Sum.inr (q,i)) j
  | Sum.inl a,j => V (Sum.inl a) j

axiom point_pair_independent {k n b degree : ℕ} {D : Type} [Fintype D]
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary)
    (hZ : Function.Injective (joinedFree (freePart V,freePart W)).mulVec) :
    Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
      (pointColumns (degree := degree) s V).mulVec uv.1+
        (pointColumns (degree := degree) s W).mulVec uv.2)

axiom pointColumns_eraseFree {k n b degree : ℕ} {D : Type} [Fintype D]
    (s : Fin b → Binary) (V : Matrix (Base k n) (Option D) Binary) :
    (changeZ (0 : Matrix (Fin n) (Fin n) Binary)).toMatrix' * pointColumns (degree := degree) s V =
      pointColumns s (eraseFree V)

axiom point_gram_ignores_free {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary) :
    (pointColumns s V).transpose*selfGram hr hd M*pointColumns s W =
      (pointColumns s (eraseFree V)).transpose*selfGram hr hd M*pointColumns s (eraseFree W)

axiom point_gram_setFree {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary)
    (Z T : Matrix (Fin n) (Option D) Binary) :
    (pointColumns s (setFree V Z)).transpose*selfGram hr hd M*pointColumns s (setFree W T) =
      (pointColumns s V).transpose*selfGram hr hd M*pointColumns s W

axiom point_pair_failure {k n b degree : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (s : Fin b → Binary) (V W : Matrix (Base k n) (Option D) Binary) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary)).toOuterMeasure
      {Z | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s (setFree V Z.1)).mulVec uv.1+
          (pointColumns (degree := degree) s (setFree W Z.2)).mulVec uv.2)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n

end Lax342547.AffineSliceIndependence
