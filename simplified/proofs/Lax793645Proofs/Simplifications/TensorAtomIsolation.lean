import Lax793645Proofs.Simplifications.TensorSubspaces

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
noncomputable section

variable {S T I S' T' : Type} [Fintype S] [Fintype T] [Fintype I]
  [Fintype S'] [Fintype T']

def selectedTensorSpace (s : I → Vec S) (t : I → Vec T) : Space (Vec (S × T)) :=
  Submodule.span F (Set.range (fun i => tensorRay (s i) (t i)))

theorem tensor_coordinates_selected [DecidableEq S'] [DecidableEq T']
    (B : Basis S' F (Vec S)) (C : Basis T' F (Vec T)) (a : S') (i : T') :
    (basisCoordinates B ⊗ₖ basisCoordinates C)*ᵥ tensorRay (B a) (C i)=
      Pi.single (a,i) 1 := by
  classical
  rw [tensor_map_ray,basisCoordinates_mulVec,basisCoordinates_mulVec]
  ext x
  by_cases ha : a=x.1 <;> by_cases hi : i=x.2 <;>
    simp [tensorRay,Pi.single_apply,Prod.ext_iff,ha,hi,eq_comm]

theorem coordinate_test_annih (Q : Mat S' S) (H : Space (Vec S)) (x : S')
    (hx : ∀ v ∈ H, (Q *ᵥ v) x=0) : Q.row x ∈ annih H := by
  rw [annih_mem]
  intro v hv
  exact hx v hv

theorem liftM_coordinate (Q : Mat S' S) (w : Mat S S) (x y : S') :
    liftM Q Q w x y=evmat w (Q.row x) (Q.row y) := by
  simp only [liftM_def,Matrix.mul_apply,Matrix.transpose_apply,evmat,Matrix.mulVec,
    dotProduct,Matrix.row_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The second tensor lemma, stated on the original spaces. A matrix killed
by quotienting both factors by the protected rectangle and the selected
atoms is the sum of those atoms and a matrix in the protected cross tensor
itself. No rank bound on the remainder is asserted or used. -/
theorem tensor_atom_isolation (U : Space (Vec S)) (V : Space (Vec T))
    (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t))
    (εS : Vec S) (εT : Vec T) (hs1 : ∀ i, dotProduct εS (s i)=1)
    (ht1 : ∀ i, dotProduct εT (t i)=1)
    (w : Mat (S × T) (S × T)) (hw : w ∈ affineTensorSpace εS εT)
    (hvan : vanish (tensorRectangle U V ⊔ selectedTensorSpace s t)
      (tensorRectangle U V ⊔ selectedTensorSpace s t) w) :
    ∃ (c : I → F) (w₀ : Mat (S × T) (S × T)),
      w=(∑ i, c i • vecMulVec (tensorRay (s i) (t i)) (tensorRay (s i) (t i)))+w₀ ∧
      w₀ ∈ box (tensorCross U V) (tensorCross U V) := by
  classical
  obtain ⟨E,B,hB,hE,hU⟩ := exists_adapted_basis U s hs
  obtain ⟨F',C,hC,hF,hV⟩ := exists_adapted_basis V t ht
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F' := Fintype.ofFinite F'
  let a (i : I) : E := ⟨s i,hE i⟩
  let b (i : I) : F' := ⟨t i,hF i⟩
  have ha (i) : B (a i)=s i := hB _
  have hb (i) : C (b i)=t i := hC _
  have hai : Function.Injective a := by
    intro i j h
    exact (LinearIndependent.of_comp U.mkQ hs).injective (congrArg Subtype.val h)
  have hbi : Function.Injective b := by
    intro i j h
    exact (LinearIndependent.of_comp V.mkQ ht).injective (congrArg Subtype.val h)
  let U' : Set E := {x | B x ∈ U}
  let V' : Set F' := {x | C x ∈ V}
  have haU (i) : a i ∉ U' := by
    intro h
    apply hs.ne_zero i
    exact (Submodule.Quotient.mk_eq_zero U).mpr (ha i ▸ h)
  have hbV (i) : b i ∉ V' := by
    intro h
    apply ht.ne_zero i
    exact (Submodule.Quotient.mk_eq_zero V).mpr (hb i ▸ h)
  let P := basisColumns B ⊗ₖ basisColumns C
  let Q := basisCoordinates B ⊗ₖ basisCoordinates C
  have hPQ : P*Q=1 := by
    dsimp only [P,Q]
    rw [←Matrix.mul_kronecker_mul,basisColumns_coordinates,basisColumns_coordinates,
      Matrix.one_kronecker_one]
  let w' := liftM Q Q w
  let eS := (basisColumns B)ᵀ *ᵥ εS
  let eT := (basisColumns C)ᵀ *ᵥ εT
  have heS (i) : eS (a i)=1 := by
    change dotProduct (B (a i)) εS=1
    rw [ha,dotProduct_comm]
    exact hs1 i
  have heT (i) : eT (b i)=1 := by
    change dotProduct (C (b i)) εT=1
    rw [hb,dotProduct_comm]
    exact ht1 i
  have hw' : TensorIdentities eS eT w' :=
    affineTensor_identities _ _ (affineTensor_basis_change B C εS εT hw)
  have hpoint (i) : Q*ᵥ tensorRay (s i) (t i)=Pi.single (a i,b i) 1 := by
    rw [←ha i,←hb i]
    exact tensor_coordinates_selected B C (a i) (b i)
  have htest (x : E × F') (hx : ¬protectedOrSelected U' V' a b x) :
      Q.row x ∈ annih (tensorRectangle U V ⊔ selectedTensorSpace s t) := by
    apply coordinate_test_annih
    have hD : tensorRectangle U V ≤ (LinearMap.proj x ∘ₗ Q.mulVecLin).ker := by
      intro v hv
      exact rectangle_coordinate_zero B C U V hU hV v hv x (fun h => hx (Or.inl h))
    have hA : selectedTensorSpace s t ≤ (LinearMap.proj x ∘ₗ Q.mulVecLin).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change (Q*ᵥ tensorRay (s i) (t i)) x=0
      rw [hpoint]
      exact Pi.single_eq_of_ne (fun h => hx (Or.inr ⟨i,h.symm⟩)) 1
    exact fun v hv => (sup_le hD hA) hv
  have hz (x y) (hx : ¬protectedOrSelected U' V' a b x)
      (hy : ¬protectedOrSelected U' V' a b y) : w' x y=0 := by
    rw [show w'=liftM Q Q w from rfl,liftM_coordinate]
    exact hvan _ (htest x hx) _ (htest y hy)
  let c := fun i => w' (a i,b i) (a i,b i)
  let z := w'-selectedDiagonal a b c
  have hzero : ∀ x y, (¬protectedCross U' V' x ∨ ¬protectedCross U' V' y) → z x y=0 :=
    tensor_isolation_coordinates w' U' V' a b hai hbi haU hbV eS eT heS heT
      hw'.selector_sym hw'.base_sym hw'.selector_diag hw'.base_diag hz
  let L' : Space (Vec (E × F')) := supportedSpace {x | B x.1 ∈ U ∨ C x.2 ∈ V}
  have hzbox : z ∈ box L' L' := by
    rw [box_mem]
    constructor
    · rintro _ ⟨v,rfl⟩ x hx
      change ∑ y, z x y*v y=0
      exact Finset.sum_eq_zero (fun y _ => by rw [hzero x y (Or.inl hx),zero_mul])
    · rintro _ ⟨v,rfl⟩ y hy
      change ∑ x, z x y*v x=0
      exact Finset.sum_eq_zero (fun x _ => by rw [hzero x y (Or.inr hy),zero_mul])
  refine ⟨c,liftM P P z,?_,?_⟩
  · have hwrec : liftM P P w'=w := by
      rw [show w'=liftM Q Q w from rfl,liftM_comp,hPQ]
      simp [liftM_def]
    have hatoms : liftM P P (selectedDiagonal a b c)=
        ∑ i, c i • vecMulVec (tensorRay (s i) (t i)) (tensorRay (s i) (t i)) := by
      rw [selectedDiagonal_sum,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,liftM_outer]
      have he : P*ᵥ Pi.single (a i,b i) 1=tensorRay (s i) (t i) := by
        rw [show P=basisColumns B ⊗ₖ basisColumns C from rfl,tensor_basis_single,ha,hb]
      rw [he]
    rw [←hatoms,←map_add]
    change w=liftM P P (selectedDiagonal a b c+(w'-selectedDiagonal a b c))
    rw [←add_sub_assoc,add_sub_cancel_left]
    exact hwrec.symm
  exact box_le (tensor_basis_supported B C U V) (tensor_basis_supported B C U V)
    (lift_mem_box P P hzbox)

end
end Lax793645Proofs.Simplifications
