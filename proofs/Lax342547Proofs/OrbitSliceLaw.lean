import Lax342547.OrbitSliceLaw
import Lax342547Proofs.FrameTuples

namespace Lax342547Proofs.OrbitSliceLaw
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.FrameTuples
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

open Lax342547.OrbitSliceLaw

/--
---
conclusion: Lax342547.OrbitSliceLaw.slice_uniform
---
-/
theorem slice_uniform {B H I J N : Type} [Fintype B] [Fintype H]
    [Fintype I] [Fintype J] [Fintype N] [DecidableEq N]
    (G : Matrix B H Binary) [Nonempty (Orbit N G)]
    (C : Matrix B I Binary) (D : Matrix H J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose*G*D))] :
    (PMF.uniformOfFintype (Orbit N G)).map (restrictOrbit G C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose*G*D)) := by
  apply FrameTuples.uniform_of_paired_action _ _ (fun c => orbitEquiv c G)
  intro c z
  exact Prod.ext (Matrix.mul_assoc c.C z.val.1 C) (Matrix.mul_assoc c.D.transpose z.val.2 D)

end
end Lax342547Proofs.OrbitSliceLaw
