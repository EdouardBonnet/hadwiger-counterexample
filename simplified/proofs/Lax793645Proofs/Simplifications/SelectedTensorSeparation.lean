import Lax793645Proofs.Simplifications.TensorQuotientReduction

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
noncomputable section

variable {S T I : Type} [Fintype S] [Fintype T] [Fintype I]

/-- Common linear extractors kill every protected direction and read off
each selected point separately. They replace sparse label-support tests. -/
theorem selected_tensor_extractors [DecidableEq I]
    (U : Space (Vec S)) (V : Space (Vec T)) (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t)) :
    ∃ E : Vec (S × T) →ₗ[F] Vec I,
      (∀ i, E (tensorRay (s i) (t i))=Pi.single i 1) ∧ tensorCross U V ≤ E.ker := by
  classical
  obtain ⟨A,B,hB,hA,hU⟩ := exists_adapted_basis U s hs
  obtain ⟨D,C,hC,hD,hV⟩ := exists_adapted_basis V t ht
  let : Fintype A := Fintype.ofFinite A
  let : Fintype D := Fintype.ofFinite D
  let a (i : I) : A := ⟨s i,hA i⟩
  let b (i : I) : D := ⟨t i,hD i⟩
  have ha (i) : B (a i)=s i := hB _
  have hb (i) : C (b i)=t i := hC _
  have hai : Function.Injective a := by
    intro i j h
    exact (LinearIndependent.of_comp U.mkQ hs).injective (congrArg Subtype.val h)
  have haU (i) : B (a i) ∉ U := by
    rw [ha]
    intro h
    exact hs.ne_zero i ((Submodule.Quotient.mk_eq_zero U).mpr h)
  have hbV (i) : C (b i) ∉ V := by
    rw [hb]
    intro h
    exact ht.ne_zero i ((Submodule.Quotient.mk_eq_zero V).mpr h)
  let Q := basisCoordinates B ⊗ₖ basisCoordinates C
  let E : Vec (S × T) →ₗ[F] Vec I := LinearMap.pi
    (fun i => LinearMap.proj (a i,b i) ∘ₗ Q.mulVecLin)
  refine ⟨E,?_,?_⟩
  · intro i
    have hp : Q*ᵥ tensorRay (s i) (t i)=Pi.single (a i,b i) 1 := by
      rw [←ha i,←hb i]
      exact tensor_coordinates_selected B C (a i) (b i)
    ext j
    change (Q*ᵥ tensorRay (s i) (t i)) (a j,b j)=(Pi.single i 1 : Vec I) j
    rw [hp]
    by_cases h : j=i
    · simp [h]
    have hab : (a j,b j) ≠ (a i,b i) := fun e => h (hai (congrArg Prod.fst e))
    simp [Pi.single_eq_of_ne h,Pi.single_eq_of_ne hab]
  intro v hv
  apply funext
  intro i
  exact cross_coordinate_zero B C U V hU hV v hv (a i,b i)
    (by rintro (h|h); exact haU i h; exact hbV i h)

theorem selected_tensor_independent_mod_cross
    (U : Space (Vec S)) (V : Space (Vec T)) (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t)) :
    LinearIndependent F ((tensorCross U V).mkQ ∘ (fun i => tensorRay (s i) (t i))) := by
  classical
  obtain ⟨E,hE,hL⟩ := selected_tensor_extractors U V s t hs ht
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hmem : (∑ j, c j • tensorRay (s j) (t j)) ∈ tensorCross U V := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (tensorCross U V).mkQ (∑ j, c j • tensorRay (s j) (t j))=0
    simpa only [map_sum,map_smul,Function.comp_apply] using hc
  have hz : E (∑ j, c j • tensorRay (s j) (t j))=0 := hL hmem
  simpa [map_sum,map_smul,hE,Pi.single_apply] using congrFun hz i

theorem selected_tensor_disjoint_cross
    (U : Space (Vec S)) (V : Space (Vec T)) (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t)) :
    Disjoint (selectedTensorSpace s t) (tensorCross U V) := by
  simpa only [selectedTensorSpace,Submodule.ker_mkQ] using Submodule.range_ker_disjoint
    (selected_tensor_independent_mod_cross U V s t hs ht)

end
end Lax793645Proofs.Simplifications
