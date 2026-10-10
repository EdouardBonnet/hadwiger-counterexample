import Lax342547.ProjectedPins
import Lax342547.ConcreteGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
---
title: Well-defined channel contractions on projected tensor spaces
type: definition and theorem
---
Two channel evaluation maps on the tensor factors determine a unique
linear contraction on their matrix tensor space. Its value is independent
of how the maps are extended to the ambient coefficient space.
-/

namespace Lax342547.TensorContractions

open Lax342547.MomentSpace Lax342547.ProjectedPins Lax342547.ConcreteGeometry

variable {B H : Type} [Fintype B] [Fintype H]

noncomputable def ambient (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Matrix B B Binary →ₗ[Binary] Binary := by
  classical
  exact matrixPair (LinearMap.BilinForm.toMatrix' ((dotProductBilin Binary Binary).compl₁₂ f g))

noncomputable def extend {S : Submodule Binary (B → Binary)} (f : S →ₗ[Binary] (H → Binary)) :
    (B → Binary) →ₗ[Binary] (H → Binary) := Classical.choose f.exists_extend

def tensor {S T : Submodule Binary (B → Binary)} (v : S) (w : T) : tensorSpace S T :=
  ⟨Matrix.vecMulVec v.val w.val, Submodule.subset_span ⟨v.val, v.property, w.val, w.property, rfl⟩⟩

noncomputable def contraction {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary)) :
    tensorSpace S T →ₗ[Binary] Binary :=
  (ambient (extend f) (extend g)).comp (tensorSpace S T).subtype

axiom ambient_outer (f g : (B → Binary) →ₗ[Binary] (H → Binary)) (v w : B → Binary) :
    ambient f g (Matrix.vecMulVec v w) = dotProduct (f v) (g w)

axiom contraction_outer {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary)) (v : S) (w : T) :
    contraction f g (tensor v w) = dotProduct (f v) (g w)

axiom extension_agreement {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary))
    (f' g' : (B → Binary) →ₗ[Binary] (H → Binary))
    (hf : f'.comp S.subtype = f) (hg : g'.comp T.subtype = g) (M : tensorSpace S T) :
    contraction f g M = ambient f' g' M.val

axiom contraction_unique {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary))
    (c : tensorSpace S T →ₗ[Binary] Binary)
    (hc : ∀ (v : S) (w : T), c (tensor v w) = dotProduct (f v) (g w)) :
    c = contraction f g

end Lax342547.TensorContractions
