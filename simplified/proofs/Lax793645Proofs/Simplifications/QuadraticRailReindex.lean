import Lax793645Proofs.Simplifications.AuxiliaryGramTrace

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {N : ℕ}

def railReindex (e : I≃J) (E : Rail I) : Rail J:=E.map (e.prodCongr e).toEmbedding

@[simp] theorem mem_rail_reindex (e : I≃J) (E : Rail I) (i j : J) :
    (i,j)∈railReindex e E ↔ (e.symm i,e.symm j)∈E:=by
  simp [railReindex]

def matrixReindex (e : I≃J) : Mat I I≃ₗ[F]Mat J J where
  toFun M:=M.submatrix e.symm e.symm
  invFun M:=M.submatrix e e
  left_inv M:=by ext i j; simp
  right_inv M:=by ext i j; simp
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def keyReindex (e : I≃J) (N : ℕ) : KeyCoordinates I N≃ₗ[F]KeyCoordinates J N where
  toFun x c:=x (c.1,(c.2.1,e.symm c.2.2))
  invFun x c:=x (c.1,(c.2.1,e c.2.2))
  left_inv x:=by funext c; simp
  right_inv x:=by funext c; simp
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem matrix_reindex_pairing (e : I≃J) (A B : Mat I I) :
    mpair (matrixReindex e A) (matrixReindex e B)=mpair A B:=by
  change (∑ i,∑ j,A (e.symm i) (e.symm j)*B (e.symm i) (e.symm j))=
    ∑ i,∑ j,A i j*B i j
  rw [Equiv.sum_comp e.symm (fun i=>∑ j,A i (e.symm j)*B i (e.symm j))]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e.symm (fun j=>A i j*B i j)

theorem gram_primitive_reindex (e : I≃J) (M : Mat I I) (x : KeyCoordinates I N) :
    gramPrimitive (matrixReindex e M) (keyReindex e N x)=gramPrimitive M x:=by
  rw [gramPrimitive,layer_form,gramPrimitive,layer_form]
  have he : (keyPlus (keyReindex e N x))ᵀ*keyMinus (keyReindex e N x)=
      matrixReindex e ((keyPlus x)ᵀ*keyMinus x):=by
    ext i j
    rfl
  rw [he,matrix_reindex_pairing]

def symmetricRailReindex (e : I≃J) (E : Rail I) :
    symmetricRail E≃ₗ[F]symmetricRail (railReindex e E) where
  toFun M:=⟨matrixReindex e M.val,
    by ext i j; exact congrFun (congrFun M.property.1 (e.symm i)) (e.symm j),
    fun i j h=>M.property.2 _ _ (by simpa using h)⟩
  invFun M:=⟨M.val.submatrix e e,
    by ext i j; exact congrFun (congrFun M.property.1 (e i)) (e j),
    fun i j h=>M.property.2 _ _ (by simpa using h)⟩
  left_inv M:=by apply Subtype.ext; ext i j; simp [matrixReindex]
  right_inv M:=by apply Subtype.ext; ext i j; simp [matrixReindex]
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem symmetric_rail_reindex_dimension (e : I≃J) (E : Rail I) :
    dim (symmetricRail (railReindex e E))=dim (symmetricRail E):=
  (symmetricRailReindex e E).finrank_eq.symm

theorem quadratic_traced_reindex (e : I≃J) (E : Rail I) (Z : Mat I I)
    (x : KeyCoordinates I N) :
    quadraticTraced (railReindex e E) (matrixReindex e Z) (keyReindex e N x) ↔
      quadraticTraced E Z x:=by
  constructor
  · intro h M hM hm
    have hh:=h (symmetricRailReindex e E ⟨M,hM,hm⟩).val
      (symmetricRailReindex e E ⟨M,hM,hm⟩).property.1
      (symmetricRailReindex e E ⟨M,hM,hm⟩).property.2
    change gramPrimitive (matrixReindex e M) _=mpair (matrixReindex e M) _ at hh
    rwa [gram_primitive_reindex,matrix_reindex_pairing] at hh
  · intro h M hM hm
    obtain ⟨A,hA⟩:=(symmetricRailReindex e E).surjective ⟨M,hM,hm⟩
    have he:=congrArg Subtype.val hA
    change matrixReindex e A.val=M at he
    rw [←he,gram_primitive_reindex,matrix_reindex_pairing]
    exact h A.val A.property.1 A.property.2

end
end Lax793645Proofs.Simplifications
