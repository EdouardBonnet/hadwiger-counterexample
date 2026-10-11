import Lax342547.ConcreteModel
import Lax342547Proofs.RawFrames
import Lax342547Proofs.RawLaw
import Lax342547.ConcreteCut
import Lax342547.FrameExistence
import Lax342547.SampledGraph
import Lax342547Proofs.HoleTriangleFree

namespace Lax342547Proofs.ConcreteModel

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.ConcreteCut Lax342547.RawFrames
open Lax342547.ConcreteModel Lax342547.HoleRelation

/--
---
conclusion: Lax342547.ConcreteModel.exists_model
---
Construct the descended testers, a frame with the concrete self-Gram
matrix, and the uniform product of frame spaces. Restrict the checked
injective frame tensor embedding to the actual cut-profile image and
use the concrete symmetric gradient form in the hole equations.
-/
theorem exists_model {k n b degree r J h N : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (hN : 2 * (Fintype.card (Coordinate k n b degree) + h) ≤ N) :
    Nonempty (Model (h := h) (N := N) hr hd M L R) := by
  classical
  obtain ⟨D⟩ := Lax342547.ConcreteCut.exists_testers (k := k) (b := b) (degree := degree) hr
  have hframe : Nonempty (Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)) :=
    Lax342547.FrameExistence.frame_nonempty_of_card_le _ (by simpa only [Fintype.card_fin] using hN)
  let : Nonempty (Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)) := hframe
  let H := RawFrames.frameHoleData (Profile k n b degree) D.role (gradient D L R)
    (Lax342547.ConcreteCut.gradient_properties D L R).1 (fun o : RawVertex (k := k) hr hd M h N => o)
  exact ⟨{
    testers := D
    frame := Classical.choice hframe
    holes := H
    role_eq := rfl
    gradient_eq := rfl
    embedding_eq := fun _ => rfl
    contraction_eq := fun _ => rfl
    hole_symmetric := fun {_ _} hij => HoleTriangleFree.hole_symmetric H hij
    law := Lax342547.RawLaw.uniformLaw (selfGram hr hd M)
    law_uniform := RawLaw.uniformLaw_apply _ }⟩

/--
---
conclusion: Lax342547.ConcreteModel.graph_indepNum_le_two
---
Apply the closed hole-triangle exclusion to this model. The graph uses
sampled positions, so repetitions among raw vertices are allowed.
-/
theorem graph_indepNum_le_two {k n b degree r J h N m : ℕ} {hr : 2 * r ≤ n} {hd : 1 ≤ degree}
    {M : Fin b → Matrix (Fin n) (Fin n) Binary}
    {L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree}
    (D : Model (h := h) (N := N) hr hd M L R) (sample : Fin m → RawVertex (k := k) hr hd M h N) :
    (graph D sample).indepNum ≤ 2 :=
  Lax342547.SampledGraph.sampleGraph_indepNum_le_two _ (fun {_ _} hij => D.hole_symmetric hij)
    (HoleTriangleFree.hole_triangle_free D.holes) sample

end Lax342547Proofs.ConcreteModel
