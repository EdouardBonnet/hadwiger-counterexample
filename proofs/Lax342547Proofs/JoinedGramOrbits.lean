import Lax342547.JoinedGramOrbits
import Lax342547Proofs.FiniteUniform

namespace Lax342547Proofs.JoinedGramOrbits
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.JoinedGramOrbits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]

/--
---
conclusion: Lax342547.JoinedGramOrbits.joined_gram
---
-/
theorem joined_gram (G : Matrix I J Binary) (H : Matrix K L Binary)
    (z : Orbit N G × Orbit N H) :
    (joined z).1.transpose*(joined z).2 =
      Matrix.fromBlocks G (z.1.val.1.transpose*z.2.val.2) (z.2.val.1.transpose*z.1.val.2) H := by
  simp only [joined,Matrix.transpose_fromCols,Matrix.fromRows_mul_fromCols,z.1.property.2.2,z.2.property.2.2]

omit [Fintype N] in
theorem left_injective (U : Matrix N (I ⊕ K) Binary) (hU : Function.Injective U.mulVec) :
    Function.Injective (U.submatrix id Sum.inl).mulVec := by
  have he : Matrix.fromCols (U.submatrix id Sum.inl) (U.submatrix id Sum.inr) = U := by
    ext n (i | k) <;> rfl
  intro x y h
  have h' : U.mulVec (Sum.elim x 0) = U.mulVec (Sum.elim y 0) := by
    rw [← he,Matrix.fromCols_mulVec,Matrix.fromCols_mulVec]
    simpa using h
  have hh := hU h'
  exact funext (fun i => congrFun hh (Sum.inl i))

omit [Fintype N] in
theorem right_injective (U : Matrix N (I ⊕ K) Binary) (hU : Function.Injective U.mulVec) :
    Function.Injective (U.submatrix id Sum.inr).mulVec := by
  have he : Matrix.fromCols (U.submatrix id Sum.inl) (U.submatrix id Sum.inr) = U := by
    ext n (i | k) <;> rfl
  intro x y h
  have h' : U.mulVec (Sum.elim 0 x) = U.mulVec (Sum.elim 0 y) := by
    rw [← he,Matrix.fromCols_mulVec,Matrix.fromCols_mulVec]
    simpa using h
  have hh := hU h'
  exact funext (fun k => congrFun hh (Sum.inr k))

def split (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    (z : Orbit N (Matrix.fromBlocks G A B H)) : Orbit N G × Orbit N H :=
  (⟨(z.val.1.submatrix id Sum.inl,z.val.2.submatrix id Sum.inl),
    left_injective _ z.property.1,left_injective _ z.property.2.1,by
      ext i j
      have hh := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) z.property.2.2
      simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix,Matrix.fromBlocks] using hh⟩,
   ⟨(z.val.1.submatrix id Sum.inr,z.val.2.submatrix id Sum.inr),
    right_injective _ z.property.1,right_injective _ z.property.2.1,by
      ext k l
      have hh := congrArg (fun M => M (Sum.inr k) (Sum.inr l)) z.property.2.2
      simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix,Matrix.fromBlocks] using hh⟩)

theorem joined_split (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    (z : Orbit N (Matrix.fromBlocks G A B H)) : joined (split G H A B z) = z.val := by
  apply Prod.ext <;> ext n (i | k) <;> rfl

def equiv (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary) :
    Orbit N (Matrix.fromBlocks G A B H) ≃ {z : Orbit N G × Orbit N H // Compatible G H A B z} where
  toFun z := ⟨split G H A B z,by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [joined_split] using z.property.1
    · simpa only [joined_split] using z.property.2.1
    · ext i l
      have hh := congrArg (fun M => M (Sum.inl i) (Sum.inr l)) z.property.2.2
      simpa [split,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix,Matrix.fromBlocks] using hh
    · ext k j
      have hh := congrArg (fun M => M (Sum.inr k) (Sum.inl j)) z.property.2.2
      simpa [split,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix,Matrix.fromBlocks] using hh⟩
  invFun z := ⟨joined z.val,z.property.1,z.property.2.1,by
    rw [Lax342547.JoinedGramOrbits.joined_gram,z.property.2.2.1,z.property.2.2.2]⟩
  left_inv z := Subtype.ext (joined_split G H A B z)
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext <;> rfl

/--
---
conclusion: Lax342547.JoinedGramOrbits.union_uniform
---
-/
theorem union_uniform (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit N (Matrix.fromBlocks G A B H))]
    [Nonempty {z : Orbit N G × Orbit N H // Compatible G H A B z}] :
    (PMF.uniformOfFintype (Orbit N (Matrix.fromBlocks G A B H))).map Subtype.val =
      (PMF.uniformOfFintype {z : Orbit N G × Orbit N H // Compatible G H A B z}).map
        (fun z => joined z.val) := by
  classical
  rw [← Lax342547Proofs.FiniteUniform.map_equiv (equiv (N := N) G H A B),PMF.map_comp]
  congr 1
  funext z
  exact (joined_split G H A B z).symm

/--
---
conclusion: Lax342547.JoinedGramOrbits.compatible_filter
---
-/
theorem compatible_filter (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit N G)] [Nonempty (Orbit N H)]
    [Nonempty (Orbit N (Matrix.fromBlocks G A B H))]
    [Nonempty {z : Orbit N G × Orbit N H // Compatible G H A B z}]
    (h : ∃ z ∈ {z : Orbit N G × Orbit N H | Compatible G H A B z},
      z ∈ (PMF.uniformOfFintype (Orbit N G × Orbit N H)).support) :
    ((PMF.uniformOfFintype (Orbit N G × Orbit N H)).filter
        {z | Compatible G H A B z} h).map joined =
      (PMF.uniformOfFintype (Orbit N (Matrix.fromBlocks G A B H))).map Subtype.val := by
  classical
  let : Nonempty ↑{z : Orbit N G × Orbit N H | Compatible G H A B z} :=
    inferInstanceAs (Nonempty {z : Orbit N G × Orbit N H // Compatible G H A B z})
  rw [Lax342547Proofs.FiniteUniform.filter_uniform,PMF.map_comp]
  exact (Lax342547.JoinedGramOrbits.union_uniform G H A B).symm

end
end Lax342547Proofs.JoinedGramOrbits
