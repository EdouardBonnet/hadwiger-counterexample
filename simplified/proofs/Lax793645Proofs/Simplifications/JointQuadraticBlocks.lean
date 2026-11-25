import Lax793645Proofs.Simplifications.QuadraticCutAnnihilators
import Mathlib.Data.Matrix.Block

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {D B : Type} [Fintype D] [Fintype B] [DecidableEq B]

def jointProjection (b : B) : Vec (D×B)→ₗ[F]Vec D where
  toFun v d:=v (d,b)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def jointInjection (b : B) : Vec D→ₗ[F]Vec (D×B) where
  toFun v x:=if x.2=b then v x.1 else 0
  map_add' _ _:=by ext x; by_cases h : x.2=b <;> simp [h]
  map_smul' _ _:=by ext x; by_cases h : x.2=b <;> simp [h]

def jointSpace (P : B→Space (Vec D)) : Space (Vec (D×B)) where
  carrier:={v | ∀ b,jointProjection b v∈P b}
  add_mem' hx hy b:= (P b).add_mem (hx b) (hy b)
  zero_mem' b:=(P b).zero_mem
  smul_mem' c x hx b:=(P b).smul_mem c (hx b)

theorem joint_projection_injection (b c : B) (v : Vec D) :
    jointProjection b (jointInjection c v)=if b=c then v else 0 := by
  ext d
  by_cases h : b=c <;> simp [jointProjection,jointInjection,h]

theorem joint_injection_mem (P : B→Space (Vec D)) (b : B) {v : Vec D} (hv : v∈P b) :
    jointInjection b v∈jointSpace P := by
  intro c
  rw [joint_projection_injection]
  by_cases hc : c=b
  · simpa [hc] using hv
  · simp [hc]

theorem joint_space_mono {P Q : B→Space (Vec D)} (h : ∀ b,P b≤Q b) :
    jointSpace P≤jointSpace Q := fun _ hv b=>h b (hv b)

theorem joint_space_inf (P Q : B→Space (Vec D)) :
    jointSpace P⊓jointSpace Q=jointSpace (fun b=>P b⊓Q b) := by
  ext v
  exact ⟨fun h b=>⟨h.1 b,h.2 b⟩,fun h=>⟨fun b=>(h b).1,fun b=>(h b).2⟩⟩

def jointMatrixBlock (b : B) : Mat (D×B) (D×B)→ₗ[F]Mat D D where
  toFun W d e:=W (d,b) (e,b)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def jointMatrixInjection (b : B) : Mat D D→ₗ[F]Mat (D×B) (D×B) where
  toFun W x y:=if x.2=b ∧ y.2=b then W x.1 y.1 else 0
  map_add' _ _:=by ext x y; by_cases h : x.2=b ∧ y.2=b <;> simp [h]
  map_smul' _ _:=by ext x y; by_cases h : x.2=b ∧ y.2=b <;> simp [h]

theorem joint_matrix_block_outer (b : B) (v w : Vec (D×B)) :
    jointMatrixBlock b (vecMulVec v w)=vecMulVec (jointProjection b v) (jointProjection b w) := rfl

theorem joint_matrix_injection_outer (b : B) (v w : Vec D) :
    jointMatrixInjection b (vecMulVec v w)=vecMulVec (jointInjection b v) (jointInjection b w) := by
  ext x y
  by_cases hx : x.2=b <;> by_cases hy : y.2=b <;>
    simp [jointMatrixInjection,jointInjection,vecMulVec,hx,hy]

theorem joint_matrix_block_diagonal (W : B→Mat D D) (b : B) :
    jointMatrixBlock b (blockDiagonal W)=W b := by
  ext d e
  exact blockDiagonal_apply_eq W d e b

theorem joint_matrix_block_rank (W : Mat (D×B) (D×B)) (b : B) :
    (jointMatrixBlock b W).rank≤W.rank :=
  Matrix.rank_submatrix_le W (fun d=>(d,b)) (fun d=>(d,b))

theorem joint_block_squares {P : Space (Vec (D×B))} {W : Mat (D×B) (D×B)}
    (hW : W∈quadraticSquares P) (b : B) :
    jointMatrixBlock b W∈quadraticSquares (P.map (jointProjection b)) := by
  induction hW using Submodule.span_induction with
  | mem W h =>
    obtain ⟨v,hv,rfl⟩:=h
    rw [joint_matrix_block_outer]
    exact Submodule.subset_span ⟨_,⟨v,hv,rfl⟩,rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

theorem joint_block_cross {K : Space (Vec (D×B))} {W : Mat (D×B) (D×B)}
    (hW : W∈quadraticCross K) (b : B) :
    jointMatrixBlock b W∈quadraticCross (K.map (jointProjection b)) := by
  induction hW using Submodule.span_induction with
  | mem W h =>
    obtain ⟨v,hv,w,rfl⟩:=h
    rw [map_add,joint_matrix_block_outer,joint_matrix_block_outer]
    exact Submodule.subset_span ⟨_,⟨v,hv,rfl⟩,_,rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

theorem joint_space_projection (P : B→Space (Vec D)) (b : B) :
    (jointSpace P).map (jointProjection b)=P b := by
  apply le_antisymm
  · rintro v ⟨x,hx,rfl⟩
    exact hx b
  · intro v hv
    exact ⟨jointInjection b v,joint_injection_mem P b hv,by simp [joint_projection_injection]⟩

theorem joint_diagonal_sum (W : B→Mat D D) :
    blockDiagonal W=∑ b,jointMatrixInjection b (W b) := by
  ext x y
  simp only [Matrix.blockDiagonal_apply,Matrix.sum_apply,jointMatrixInjection,LinearMap.coe_mk,
    AddHom.coe_mk]
  by_cases h : x.2=y.2
  · simp [h]
  · simp [h,show ∀ b,¬(x.2=b ∧ y.2=b) from fun b hb=>h (hb.1.trans hb.2.symm)]

theorem joint_diagonal_squares (P : B→Space (Vec D)) (W : B→Mat D D)
    (hW : ∀ b,W b∈quadraticSquares (P b)) : blockDiagonal W∈quadraticSquares (jointSpace P) := by
  rw [joint_diagonal_sum]
  apply Submodule.sum_mem
  intro b _
  have hi {M : Mat D D} (hm : M∈quadraticSquares (P b)) :
      jointMatrixInjection b M∈quadraticSquares (jointSpace P) := by
    induction hm using Submodule.span_induction with
    | mem W h =>
      obtain ⟨v,hv,rfl⟩:=h
      rw [joint_matrix_injection_outer]
      exact Submodule.subset_span ⟨_,joint_injection_mem P b hv,rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx
  exact hi (hW b)

theorem joint_diagonal_mulVec (W : B→Mat D D) (v : Vec (D×B)) (b : B) :
    jointProjection b (blockDiagonal W*ᵥv)=W b*ᵥ(jointProjection b v) := by
  ext d
  simp [jointProjection,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.blockDiagonal_apply]

theorem joint_diagonal_columns (P : B→Space (Vec D)) (W : B→Mat D D)
    (hW : ∀ b,colSp (W b)≤P b) : colSp (blockDiagonal W)≤jointSpace P := by
  rintro v ⟨x,rfl⟩ b
  change jointProjection b (blockDiagonal W*ᵥx)∈P b
  rw [joint_diagonal_mulVec]
  exact hW b ⟨_,rfl⟩

def jointSpaceEquiv (P : B→Space (Vec D)) : jointSpace P≃ₗ[F](∀ b,P b) where
  toFun x b:=⟨jointProjection b x.val,x.property b⟩
  invFun x:=⟨fun d=>(x d.2).val d.1,fun b=>(x b).property⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem joint_space_dimension (P : B→Space (Vec D)) :
    dim (jointSpace P)=∑ b,dim (P b) := by
  unfold dim
  rw [(jointSpaceEquiv P).finrank_eq]
  exact Module.finrank_pi_fintype F

theorem joint_diagonal_rank_le (W : B→Mat D D) :
    (blockDiagonal W).rank≤∑ b,(W b).rank := by
  rw [←colSp_dim]
  calc
    _ ≤ dim (jointSpace (fun b=>colSp (W b))):=
      Submodule.finrank_mono (joint_diagonal_columns _ W (fun _=>le_rfl))
    _ = _:=by simp only [joint_space_dimension,colSp_dim]

theorem joint_diagonal_fixes (W : B→Mat D D) (P : Space (Vec (D×B)))
    (h : ∀ b,∀ v∈P.map (jointProjection b),W b*ᵥv=v) :
    ∀ v∈P,blockDiagonal W*ᵥv=v := by
  intro v hv
  ext d
  have hh:=joint_diagonal_mulVec W v d.2
  rw [h d.2 _ ⟨v,hv,rfl⟩] at hh
  exact congrFun hh d.1

theorem joint_diagonal_lift (D₀ W : B→Mat D D) :
    liftM (blockDiagonal D₀) (blockDiagonal D₀) (blockDiagonal W)=
      blockDiagonal (fun b=>liftM (D₀ b) (D₀ b) (W b)) := by
  simp only [liftM_def,Matrix.blockDiagonal_transpose,←Matrix.blockDiagonal_mul]

def jointProjectionCover (P : Space (Vec (D×Bool))) : Space (Vec D) :=
  P.map (jointProjection false)⊔P.map (jointProjection true)

theorem joint_projection_le_cover (P : Space (Vec (D×Bool))) (b : Bool) :
    P.map (jointProjection b)≤jointProjectionCover P := by
  cases b
  · exact le_sup_left
  · exact le_sup_right

theorem joint_projection_cover_dimension (P : Space (Vec (D×Bool))) :
    dim (jointProjectionCover P)≤2*dim P := by
  have h:=Submodule.finrank_sup_add_finrank_inf_eq
    (P.map (jointProjection false)) (P.map (jointProjection true))
  have h₁:=Submodule.finrank_map_le (jointProjection false) P
  have h₂:=Submodule.finrank_map_le (jointProjection true) P
  change dim (P.map (jointProjection false)⊔P.map (jointProjection true) : Space (Vec D))+
    dim (P.map (jointProjection false)⊓P.map (jointProjection true) : Space (Vec D))=
    dim (P.map (jointProjection false))+dim (P.map (jointProjection true)) at h
  change dim (P.map (jointProjection false)⊔P.map (jointProjection true) : Space (Vec D))≤2*dim P
  simp only [dim] at *
  omega

theorem joint_constraints_project (P : B→Space (Vec D)) (K : Space (Vec (D×B)))
    {W : Mat (D×B) (D×B)} (hW : W∈quadraticSquares (jointSpace P)⊔quadraticCross K)
    (b : B) : jointMatrixBlock b W∈quadraticSquares (P b)⊔quadraticCross (K.map (jointProjection b)) := by
  obtain ⟨S,hS,T,hT,rfl⟩:=Submodule.mem_sup.mp hW
  rw [map_add]
  exact Submodule.add_mem_sup (by simpa only [joint_space_projection] using joint_block_squares hS b)
    (joint_block_cross hT b)

theorem quadratic_cross_top_squares (K : Space (Vec D)) :
    quadraticCross K≤quadraticSquares (⊤ : Space (Vec D)) := by
  apply Submodule.span_le.mpr
  rintro W ⟨v,_,w,rfl⟩
  have hs (a : Vec D) : vecMulVec a a∈quadraticSquares (⊤ : Space (Vec D)) :=
    Submodule.subset_span ⟨a,Submodule.mem_top,rfl⟩
  have he : vecMulVec v w+vecMulVec w v=
      vecMulVec (v+w) (v+w)-vecMulVec v v-vecMulVec w w := by
    rw [vecMulVec_add,add_vecMulVec,add_vecMulVec]
    abel
  rw [he]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ (hs _) (hs _)) (hs _)

theorem quadratic_constraints_top_squares (P K : Space (Vec D)) :
    quadraticSquares P⊔quadraticCross K≤quadraticSquares (⊤ : Space (Vec D)) :=
  sup_le (quadratic_squares_mono le_top) (quadratic_cross_top_squares K)

theorem pin_selected_inf {P A L : Space (Vec D)} (hP : P≤L) (hA : Disjoint A L) :
    (P⊔A)⊓L=P := by
  apply le_antisymm
  · rintro x ⟨hx,hxL⟩
    obtain ⟨p,hp,a,ha,he⟩:=Submodule.mem_sup.mp hx
    have hpa : p+a∈L:=he.symm ▸ hxL
    have haL : a∈L:=by simpa only [add_sub_cancel_left] using L.sub_mem hpa (hP hp)
    have ha0 : a=0:=hA.le_bot ⟨ha,haL⟩
    simpa [←he,ha0] using hp
  · exact le_inf le_sup_left hP

theorem quadratic_global_residual (P K L : Space (Vec D)) (hK : K≤P)
    (hKL : Disjoint K L) {W : Mat D D}
    (hW : W∈quadraticSquares P⊔quadraticCross K) (hcol : colSp W≤L) :
    W∈quadraticSquares (P⊓L) := by
  have htop := quadratic_constraints_top_squares P K hW
  have hL := quadraticSquares_project htop hcol
  have hh : W∈(quadraticSquares P⊔quadraticCross K)⊓quadraticSquares L:=⟨hW,hL⟩
  rwa [quadratic_kernel_intersection P K L hK hKL] at hh

end
end Lax793645Proofs.Simplifications
