import Lax793645Proofs.Simplifications.ProtectedTensorSpaces
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
noncomputable section

variable {S I : Type} [Fintype S] [Fintype I]

/-- A basis simultaneously adapted to a protected space and vectors
independent modulo that space. Its index set consists of the basis vectors
themselves, so no choice of a distinguished constant basis vector is made. -/
theorem exists_adapted_basis (U : Space (Vec S)) (p : I → Vec S)
    (hp : LinearIndependent F (U.mkQ ∘ p)) :
    ∃ (E : Set (Vec S)) (B : Basis E F (Vec S)),
      (∀ e, B e=e.val) ∧ (∀ i, p i ∈ E) ∧
      Submodule.span F (B '' {e | B e ∈ U})=U := by
  classical
  let b := Module.finBasis F U
  let u : Fin (dim U) → Vec S := fun i => (b i).val
  have hu : LinearIndependent F u := b.linearIndependent.map' U.subtype (by simp)
  have hspan : Submodule.span F (Set.range u)=U := by
    have hb := congrArg (Submodule.map U.subtype) b.span_eq
    simpa only [Submodule.map_span,← Set.range_comp,Submodule.map_top,
      Submodule.range_subtype,u,Function.comp_def,Submodule.subtype_apply] using hb
  have hdis : Disjoint (Submodule.span F (Set.range u))
      (Submodule.span F (Set.range p)) := by
    rw [hspan]
    have h := (Submodule.range_ker_disjoint hp).symm
    simpa only [Submodule.ker_mkQ] using h
  have hli := hu.sum_type (LinearIndependent.of_comp U.mkQ hp) hdis
  let f := Sum.elim u p
  let hs := hli.linearIndepOn_id
  let E := hs.extend (Set.subset_univ (Set.range f))
  let B : Basis E F (Vec S) := Basis.extend hs
  have hmem (i : Fin (dim U) ⊕ I) : f i ∈ E := hs.subset_extend _ ⟨i,rfl⟩
  have hB (e : E) : B e=e.val := Basis.extend_apply_self hs e
  refine ⟨E,B,hB,fun i => hmem (Sum.inr i),?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,he,rfl⟩
    exact he
  apply le_trans hspan.symm.le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨u i,by simpa only [f,Sum.elim_inl] using hmem (Sum.inl i)⟩,?_,?_⟩
  · change B _ ∈ U
    rw [hB]
    exact (b i).property
  · exact hB _

end
end Lax793645Proofs.Simplifications
