import Lax342547.FrozenValues
import Lax342547Proofs.RawFrames
import Lax342547Proofs.PairedWitnesses
import Lax342547.Atoms
import Lax342547.RawContractions
import Lax342547.TensorContractions

namespace Lax342547Proofs.FrozenValues

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.WitnessAtoms
open Lax342547.ExactPins Lax342547.TableContractions Lax342547.RawContractions Lax342547.RawBaselines
open Lax342547.PairedKeys Lax342547.KeySpans Lax342547.TableSpaces Lax342547.RawFrames

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}
  {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

omit [Fintype H] in
theorem key_mem (W : Lists k n b degree r hr) (e : Component (Tag k))
    (i z : Fin 2) (t : Fin (W.length i z)) (htag : (W.left i z t).tag ∈ e.val) :
    primalEmbedding (H := H) i (W.left i z t).vector ∈ keys W e := by
  classical
  apply Submodule.subset_span
  refine ⟨⟨i, z, t⟩, ?_⟩
  simp [direction, htag, ray, labels, bases, PointAtom.vector]

/--
---
conclusion: Lax342547.FrozenValues.frozen_atom
---
In each incident component both primal key directions are frozen.
Thus both channel evaluation vectors are unchanged. Their dot product
is the outer-product contraction of that atom; other components vanish.
-/
theorem frozen_atom (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hfrozen : Frozen F W P Q oA oB) (i z z' : Fin 2) (t : Fin (W.length i z')) :
    fullContraction F (Profile k n b degree) i z (W.left i z' t).profile =
      fullContraction (rawForms oA oB) (Profile k n b degree) i z (W.left i z' t).profile := by
  classical
  simp only [fullContraction, LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ e, Lax342547.TensorContractions.ambient (fullPlus F e i z) (fullMinus F e i z)
      ((W.left i z' t).profile.val e)) =
    ∑ e, Lax342547.TensorContractions.ambient (fullPlus (rawForms oA oB) e i z)
      (fullMinus (rawForms oA oB) e i z) ((W.left i z' t).profile.val e)
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : (W.left i z' t).tag ∈ e.val
  · have hmem := key_mem (H := H) W e i z' t he
    have hp : fullPlus F e i z (W.left i z' t).vector =
        fullPlus (rawForms oA oB) e i z (W.left i z' t).vector := by
      funext h
      exact (hfrozen e).1 _ _ (Or.inl
        ((show keys W e ≤ P.space (e, true) ⊔ keys W e from le_sup_right) hmem))
    have hm : fullMinus F e i z (W.left i z' t).vector =
        fullMinus (rawForms oA oB) e i z (W.left i z' t).vector := by
      funext h
      exact (hfrozen e).2 _ _ (Or.inr
        ((show keys W e ≤ P.space (e, false) ⊔ keys W e from le_sup_right) hmem))
    simp only [PointAtom.profile, Lax342547.Atoms.atom_component, he, if_pos]
    change Lax342547.TensorContractions.ambient (fullPlus F e i z) (fullMinus F e i z)
      (Matrix.vecMulVec (W.left i z' t).vector (W.left i z' t).vector) =
      Lax342547.TensorContractions.ambient (fullPlus (rawForms oA oB) e i z)
        (fullMinus (rawForms oA oB) e i z)
        (Matrix.vecMulVec (W.left i z' t).vector (W.left i z' t).vector)
    rw [Lax342547.TensorContractions.ambient_outer, Lax342547.TensorContractions.ambient_outer]
    rw [hp, hm]
  · simp [PointAtom.profile, Lax342547.Atoms.atom_component, he]

/--
---
conclusion: Lax342547.FrozenValues.selected_values
---
The frozen contraction equals the actual one. The positionwise matched
keys identify its tensor with the opposite matched atom's tensor. On
that endpoint self-contraction is zero; on the other endpoint it is the
matched atom's own-unit contraction.
-/
theorem selected_values (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (i z z' : Fin 2) (t : Fin (W.length i z')) :
    fullContraction F (Profile k n b degree) i z (W.left i z' t).profile =
      if z = z' then 0 else ownContraction oB z' (W.right i z' t).profile := by
  classical
  rw [Lax342547.FrozenValues.frozen_atom W P Q oA oB F hfrozen i z z' t,
    Lax342547.RawContractions.raw_contraction]
  have he := PairedWitnesses.atom_sharing (oA i) (oB z') (W.left i z' t) (W.right i z' t)
    (W.same_tag i z' t) (hkeys i z' t)
  rw [he]
  by_cases hzz : z = z'
  · subst z
    rw [if_pos rfl]
    exact RawFrames.profileContraction_zero (oB z') _
  · rw [if_neg hzz]
    have hz : z = other z' := by fin_cases z <;> fin_cases z' <;> simp_all [other]
    subst z
    rfl

end Lax342547Proofs.FrozenValues
