import Lax342547.RawFrames
import Lax342547Proofs.HoleTriangleFree
import Lax342547.SampledGraph

namespace Lax342547Proofs.RawFrames

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] {Comp : Type}
variable {E : Matrix B B Binary}

theorem primal_injective (F : Frame B H N E) : Function.Injective F.P.mulVec := by
  intro x y h
  have h' : (x, (0 : H → Binary)) = (y, 0) := F.plus_injective (by simpa using h)
  exact congrArg Prod.fst h'

theorem dual_injective (F : Frame B H N E) : Function.Injective F.Q.mulVec := by
  intro x y h
  have h' : (x, (0 : H → Binary)) = (y, 0) := F.minus_injective (by simpa using h)
  exact congrArg Prod.fst h'

omit [Fintype N] in
theorem left_mul_injective {C : Type} (P : Matrix N B Binary)
    (hP : Function.Injective P.mulVec) :
    Function.Injective (fun Z : Matrix B C Binary => P * Z) := by
  intro Z W h
  ext i j
  apply congrFun (hP ?_) i
  exact funext (fun r => congrArg (fun A : Matrix N C Binary => A r j) h)

theorem sandwich_injective (F : Frame B H N E) :
    Function.Injective (sandwich F.P F.Q) := by
  intro Z W h
  have h₁ : Z * F.Q.transpose = W * F.Q.transpose :=
    left_mul_injective F.P (primal_injective F) (by simpa [sandwich, Matrix.mul_assoc] using h)
  have h₂ : F.Q * Z.transpose = F.Q * W.transpose := by
    simpa using congrArg Matrix.transpose h₁
  have h₃ := left_mul_injective F.Q (dual_injective F) h₂
  simpa using congrArg Matrix.transpose h₃

theorem contraction_sandwich (F : Frame B H N E) (Z : Matrix B B Binary) :
    contraction F (sandwich F.P F.Q Z) = 0 := by
  have ha : F.Y.transpose * F.P = 0 := by
    simpa using congrArg Matrix.transpose F.minus_annihilator
  change Matrix.trace (F.X * F.Y.transpose * (F.P * Z * F.Q.transpose)) = 0
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc F.X F.Y.transpose F.P,
    ha, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]

theorem profileMap_injective (F : Comp → Frame B H N E) :
    Function.Injective (profileMap F) := by
  intro x y h
  funext e
  exact sandwich_injective (F e) (congrFun h e)

theorem profileContraction_zero [Fintype Comp] (F : Comp → Frame B H N E)
    (x : Comp → Matrix B B Binary) : profileContraction F (profileMap F x) = 0 := by
  simp [profileContraction, profileMap, contraction_sandwich]

/--
---
conclusion: Lax342547.RawFrames.tensor_realization
---
Injectivity of the two primal frames recovers each column and row of the
coefficient matrix. Transposing the minus annihilator gives $Y^TP=0$,
which makes every self-contraction vanish.
-/
theorem tensor_realization (F : Comp → Frame B H N E) [Fintype Comp] :
    Function.Injective (profileMap F) ∧
      ∀ x, profileContraction F (profileMap F x) = 0 :=
  ⟨profileMap_injective F, profileContraction_zero F⟩

open Lax342547.HoleRelation Lax342547.SampledGraph

def frameHoleData {Ω : Type} [Fintype Comp]
    (X : Submodule Binary (Comp → Matrix B B Binary))
    (a : X →ₗ[Binary] Binary) (T : LinearMap.BilinForm Binary X)
    (hT : ∀ x y, T x y = T y x) (F : Ω → Comp → Frame B H N E) :
    HoleData Ω X (Comp → Matrix N N Binary) where
  a := a
  T := T
  symmetric := hT
  U o := (profileMap (F o)).comp X.subtype
  injective o := (profileMap_injective (F o)).comp X.subtype_injective
  u o := profileContraction (F o)

theorem frame_sample_indepNum_le_two {Ω : Type} [Fintype Comp]
    (X : Submodule Binary (Comp → Matrix B B Binary))
    (a : X →ₗ[Binary] Binary) (T : LinearMap.BilinForm Binary X)
    (hT : ∀ x y, T x y = T y x) (F : Ω → Comp → Frame B H N E)
    {m : ℕ} (sample : Fin m → Ω) :
    let D := frameHoleData X a T hT F
    (sampleGraph (Hole D) (HoleTriangleFree.hole_symmetric D) sample).indepNum ≤ 2 := by
  dsimp only
  exact Lax342547.SampledGraph.sampleGraph_indepNum_le_two _ _
    (HoleTriangleFree.hole_triangle_free _) sample

end Lax342547Proofs.RawFrames
