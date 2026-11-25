import Lax793645Proofs.Simplifications.TensorCoordinateChanges

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
noncomputable section

variable {S T S' T' : Type} [Fintype S] [Fintype T] [Fintype S'] [Fintype T']

def flattenMatrix : Mat S T ≃ₗ[F] Vec (S × T) where
  toFun M x := M x.1 x.2
  invFun x a i := x (a,i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tensorRectangle (U : Space (Vec S)) (V : Space (Vec T)) : Space (Vec (S × T)) :=
  (box U V).map flattenMatrix.toLinearMap

def tensorCross (U : Space (Vec S)) (V : Space (Vec T)) : Space (Vec (S × T)) :=
  tensorRectangle U ⊤ ⊔ tensorRectangle ⊤ V

theorem tensorRay_rectangle (U : Space (Vec S)) (V : Space (Vec T))
    (s : Vec S) (t : Vec T) (hs : s ∈ U) (ht : t ∈ V) :
    tensorRay s t ∈ tensorRectangle U V :=
  ⟨vecMulVec s t,outer_in_box s t hs ht,rfl⟩

theorem tensorRay_cross (U : Space (Vec S)) (V : Space (Vec T))
    (s : Vec S) (t : Vec T) (h : s ∈ U ∨ t ∈ V) :
    tensorRay s t ∈ tensorCross U V := by
  rcases h with h|h
  · exact Submodule.mem_sup_left (tensorRay_rectangle U ⊤ s t h Submodule.mem_top)
  · exact Submodule.mem_sup_right (tensorRay_rectangle ⊤ V s t Submodule.mem_top h)

def supportedSpace (P : Set S) : Space (Vec S) where
  carrier := {v | ∀ i, i ∉ P → v i=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi,hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

theorem basis_coordinate_zero (B : Basis S' F (Vec S)) (U : Space (Vec S))
    (hU : Submodule.span F (B '' {a | B a ∈ U})=U)
    (v : Vec S) (hv : v ∈ U) (a : S') (ha : B a ∉ U) : B.equivFun v a=0 := by
  classical
  rw [← hU] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨j,hj,rfl⟩ := hv
      have hja : j ≠ a := by intro h; subst j; exact ha hj
      simp [Basis.equivFun_apply,hja]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add,Pi.add_apply,hx,hy,add_zero]
  | smul c x _ hx => simp only [map_smul,Pi.smul_apply,smul_eq_mul,hx,mul_zero]

theorem basis_coordinate_image (B : Basis S' F (Vec S)) (U : Space (Vec S))
    (hU : Submodule.span F (B '' {a | B a ∈ U})=U) :
    U.map (basisCoordinates B).mulVecLin ≤ supportedSpace {a | B a ∈ U} := by
  rintro _ ⟨v,hv,rfl⟩ a ha
  exact (congrFun (basisCoordinates_mulVec B v) a).trans
    (basis_coordinate_zero B U hU v hv a ha)

theorem tensor_map_flatten (A : Mat S' S) (B : Mat T' T) (M : Mat S T) :
    (A ⊗ₖ B)*ᵥ flattenMatrix M=flattenMatrix (liftM A B M) := by
  funext x
  change (∑ z : S × T, (A x.1 z.1*B x.2 z.2)*M z.1 z.2)=
    ∑ i : T, (∑ a : S, A x.1 a*M a i)*B x.2 i
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem rectangle_coordinate_zero (B : Basis S' F (Vec S)) (C : Basis T' F (Vec T))
    (U : Space (Vec S)) (V : Space (Vec T))
    (hU : Submodule.span F (B '' {a | B a ∈ U})=U)
    (hV : Submodule.span F (C '' {i | C i ∈ V})=V)
    (v : Vec (S × T)) (hv : v ∈ tensorRectangle U V) (x : S' × T')
    (hx : ¬(B x.1 ∈ U ∧ C x.2 ∈ V)) :
    ((basisCoordinates B ⊗ₖ basisCoordinates C)*ᵥ v) x=0 := by
  classical
  obtain ⟨M,hM,rfl⟩ := hv
  rw [show flattenMatrix.toLinearMap M=flattenMatrix M from rfl,tensor_map_flatten]
  let M' := liftM (basisCoordinates B) (basisCoordinates C) M
  have hM' : M' ∈ box (supportedSpace {a | B a ∈ U}) (supportedSpace {i | C i ∈ V}) :=
    box_le (basis_coordinate_image B U hU) (basis_coordinate_image C V hV)
      (lift_mem_box _ _ hM)
  obtain ⟨hcol,hrow⟩ := (box_mem ..).mp hM'
  change M' x.1 x.2=0
  by_cases ha : B x.1 ∈ U
  · exact hrow (colSp_mem x.1) x.2 (fun hb => hx ⟨ha,hb⟩)
  · exact hcol (colSp_mem x.2) x.1 ha

theorem tensor_basis_single [DecidableEq S'] [DecidableEq T']
    (B : Basis S' F (Vec S)) (C : Basis T' F (Vec T))
    (x : S' × T') :
    (basisColumns B ⊗ₖ basisColumns C)*ᵥ Pi.single x 1=tensorRay (B x.1) (C x.2) := by
  classical
  funext y
  simp [Matrix.mulVec_single,Matrix.col_apply,basisColumns,tensorRay]

theorem cross_coordinate_zero (B : Basis S' F (Vec S)) (C : Basis T' F (Vec T))
    (U : Space (Vec S)) (V : Space (Vec T))
    (hU : Submodule.span F (B '' {a | B a ∈ U})=U)
    (hV : Submodule.span F (C '' {i | C i ∈ V})=V)
    (v : Vec (S × T)) (hv : v ∈ tensorCross U V) (x : S' × T')
    (hx : ¬(B x.1 ∈ U ∨ C x.2 ∈ V)) :
    ((basisCoordinates B ⊗ₖ basisCoordinates C)*ᵥ v) x=0 := by
  have htopB : Submodule.span F (B '' {a | B a ∈ (⊤ : Space (Vec S))})=⊤ := by
    simpa using B.span_eq
  have htopC : Submodule.span F (C '' {a | C a ∈ (⊤ : Space (Vec T))})=⊤ := by
    simpa using C.span_eq
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add,Pi.add_apply,
    rectangle_coordinate_zero B C U ⊤ hU htopC u hu x (fun h => hx (Or.inl h.1)),
    rectangle_coordinate_zero B C ⊤ V htopB hV z hz x (fun h => hx (Or.inr h.2)),add_zero]

theorem tensor_basis_supported (B : Basis S' F (Vec S)) (C : Basis T' F (Vec T))
    (U : Space (Vec S)) (V : Space (Vec T)) :
    (supportedSpace {x | B x.1 ∈ U ∨ C x.2 ∈ V}).map
      (basisColumns B ⊗ₖ basisColumns C).mulVecLin ≤ tensorCross U V := by
  classical
  rintro _ ⟨v,hv,rfl⟩
  have he : v=∑ x, v x • (Pi.single x 1 : Vec (S' × T')) := by
    ext y; simp [Pi.single_apply]
  rw [he,map_sum]
  apply Submodule.sum_mem
  intro x _
  rw [map_smul,Matrix.mulVecLin_apply,tensor_basis_single]
  by_cases hx : B x.1 ∈ U ∨ C x.2 ∈ V
  · exact Submodule.smul_mem _ _ (tensorRay_cross U V _ _ hx)
  · rw [hv x hx,zero_smul]
    exact Submodule.zero_mem _

end
end Lax793645Proofs.Simplifications
