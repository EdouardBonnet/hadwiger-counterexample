import Lax342547.FrameTuples

/-!
---
title: Exact reference Gram-orbit marginals under injective affine restrictions
type: definition and theorem
---
An injective coefficient restriction of a uniform full paired Gram orbit
has exactly the uniform prescribed slice law. The simultaneous ambient
action preserves the full Gram and transports every restriction fiber.
-/

namespace Lax342547.OrbitSliceLaw
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.FrameTuples
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false


def restrictOrbit {B H I J N : Type} [Fintype B] [Fintype H]
    [Fintype I] [Fintype J] [Fintype N] (G : Matrix B H Binary)
    (C : Matrix B I Binary) (D : Matrix H J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (z : Orbit N G) : Orbit N (C.transpose*G*D) :=
  ⟨(z.val.1*C,z.val.2*D),by
    refine ⟨?_,?_,?_⟩
    · intro x y hh
      apply hC
      apply z.property.1
      simpa only [Matrix.mulVec_mulVec] using hh
    · intro x y hh
      apply hD
      apply z.property.2.1
      simpa only [Matrix.mulVec_mulVec] using hh
    · simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc z.val.1.transpose,z.property.2.2]⟩

def changeOrbit {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]
    (c : Change N) (G : Matrix B H Binary) (z : Orbit N G) : Orbit N G :=
  ⟨(c.C*z.val.1,c.D.transpose*z.val.2),by
    refine ⟨?_,?_,?_⟩
    · intro x y hh
      apply z.property.1
      apply c.injective
      simpa only [Matrix.mulVec_mulVec] using hh
    · intro x y hh
      apply z.property.2.1
      apply c.dual_injective
      simpa only [Matrix.mulVec_mulVec] using hh
    · have he : c.C.transpose*c.D.transpose = 1 := by simpa using congrArg Matrix.transpose c.DC
      simp only [Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc c.C.transpose,
        he,Matrix.one_mul,z.property.2.2]⟩

def orbitEquiv {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]
    (c : Change N) (G : Matrix B H Binary) : Orbit N G ≃ Orbit N G where
  toFun := changeOrbit c G
  invFun := changeOrbit c.inv G
  left_inv z := by
    apply Subtype.ext
    have he : c.C.transpose*c.D.transpose = 1 := by simpa using congrArg Matrix.transpose c.DC
    apply Prod.ext <;> simp [changeOrbit,Change.inv,← Matrix.mul_assoc,c.DC,he]
  right_inv z := by
    apply Subtype.ext
    have he : c.D.transpose*c.C.transpose = 1 := by simpa using congrArg Matrix.transpose c.CD
    apply Prod.ext <;> simp [changeOrbit,Change.inv,← Matrix.mul_assoc,c.CD,he]

axiom slice_uniform {B H I J N : Type} [Fintype B] [Fintype H]
    [Fintype I] [Fintype J] [Fintype N] [DecidableEq N]
    (G : Matrix B H Binary) [Nonempty (Orbit N G)]
    (C : Matrix B I Binary) (D : Matrix H J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose*G*D))] :
    (PMF.uniformOfFintype (Orbit N G)).map (restrictOrbit G C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose*G*D))

end
end Lax342547.OrbitSliceLaw
