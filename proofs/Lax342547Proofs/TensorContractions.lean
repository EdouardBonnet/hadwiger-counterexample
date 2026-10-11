import Lax342547.TensorContractions
import Lax342547Proofs.UnaryMixer

namespace Lax342547Proofs.TensorContractions

open Lax342547.MomentSpace Lax342547.ProjectedPins Lax342547.TensorContractions

variable {B H : Type} [Fintype B] [Fintype H]

/--
---
conclusion: Lax342547.TensorContractions.ambient_outer
---
The matrix of the pulled-back channel dot product evaluates on an outer
product as that bilinear form on its two generating vectors.
-/
theorem ambient_outer (f g : (B → Binary) →ₗ[Binary] (H → Binary)) (v w : B → Binary) :
    ambient f g (Matrix.vecMulVec v w) = dotProduct (f v) (g w) := by
  classical
  rw [ambient, UnaryMixer.matrixPair_vecMulVec, Matrix.toBilin'_toMatrix']
  rfl

omit [Fintype B] [Fintype H] in
theorem extend_apply {S : Submodule Binary (B → Binary)} (f : S →ₗ[Binary] (H → Binary)) (v : S) :
    extend f v.val = f v := congrArg (fun l : S →ₗ[Binary] (H → Binary) => l v)
      (Classical.choose_spec f.exists_extend)

/--
---
conclusion: Lax342547.TensorContractions.contraction_outer
---
The chosen ambient extensions agree with their original maps on the two
factor spaces, so their outer-product contraction is the required dot product.
-/
theorem contraction_outer {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary)) (v : S) (w : T) :
    contraction f g (tensor v w) = dotProduct (f v) (g w) := by
  change ambient (extend f) (extend g) (Matrix.vecMulVec v.val w.val) = _
  rw [Lax342547.TensorContractions.ambient_outer, extend_apply, extend_apply]

omit [Fintype B] in
theorem ambient_ext {S T : Submodule Binary (B → Binary)}
    (f g : Matrix B B Binary →ₗ[Binary] Binary)
    (h : ∀ (v : S) (w : T), f (Matrix.vecMulVec v.val w.val) = g (Matrix.vecMulVec v.val w.val))
    (M : Matrix B B Binary) (hM : M ∈ tensorSpace S T) : f M = g M := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨v, hv, w, hw, rfl⟩ := hM
    exact h ⟨v, hv⟩ ⟨w, hw⟩
  | zero => simp only [map_zero]
  | add M M' _ _ ih ih' => simp only [map_add, ih, ih']
  | smul c M _ ih => simp only [map_smul, ih]

/--
---
conclusion: Lax342547.TensorContractions.extension_agreement
---
Any two ambient extensions agree on every generating outer product.
Linearity extends this equality to the whole projected tensor space.
-/
theorem extension_agreement {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary))
    (f' g' : (B → Binary) →ₗ[Binary] (H → Binary))
    (hf : f'.comp S.subtype = f) (hg : g'.comp T.subtype = g) (M : tensorSpace S T) :
    contraction f g M = ambient f' g' M.val := by
  apply ambient_ext (ambient (extend f) (extend g)) (ambient f' g') ?_ M.val M.property
  intro v w
  have hf' := congrArg (fun l : S →ₗ[Binary] (H → Binary) => l v) hf
  have hg' := congrArg (fun l : T →ₗ[Binary] (H → Binary) => l w) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hf' hg'
  rw [Lax342547.TensorContractions.ambient_outer, Lax342547.TensorContractions.ambient_outer, extend_apply, extend_apply, hf', hg']

/--
---
conclusion: Lax342547.TensorContractions.contraction_unique
---
Extend the proposed functional linearly to all matrices. Its values on
the outer-product generators agree with the constructed contraction,
which determines its restriction to their span uniquely.
-/
theorem contraction_unique {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary))
    (c : tensorSpace S T →ₗ[Binary] Binary)
    (hc : ∀ (v : S) (w : T), c (tensor v w) = dotProduct (f v) (g w)) :
    c = contraction f g := by
  obtain ⟨c', hc'⟩ := c.exists_extend
  ext M
  have he := congrArg (fun l : tensorSpace S T →ₗ[Binary] Binary => l M) hc'
  change c' M.val = c M at he
  rw [← he]
  apply ambient_ext c' (ambient (extend f) (extend g)) ?_ M.val M.property
  intro v w
  have hvw := congrArg (fun l : tensorSpace S T →ₗ[Binary] Binary => l (tensor v w)) hc'
  change c' (Matrix.vecMulVec v.val w.val) = c (tensor v w) at hvw
  rw [hvw, hc, Lax342547.TensorContractions.ambient_outer, extend_apply, extend_apply]

end Lax342547Proofs.TensorContractions
