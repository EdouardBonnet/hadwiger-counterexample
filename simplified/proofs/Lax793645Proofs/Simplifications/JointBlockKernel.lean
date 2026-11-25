import Lax793645Proofs.Simplifications.JointQuadraticBlocks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {D B : Type} [Fintype D] [Fintype B] [DecidableEq D] [DecidableEq B]

theorem joint_injection_dot (i : B) (u : Vec D) (v : Vec (D×B)) :
    dotProduct (jointInjection i u) v=dotProduct u (jointProjection i v) := by
  simp [dotProduct,Fintype.sum_prod_type,jointInjection,jointProjection]

theorem joint_injection_annih (S : B→Space (Vec D)) (i : B) {u : Vec D}
    (hu : u∈annih (S i)) : jointInjection i u∈annih (jointSpace S) := by
  apply (annih_mem _ _).mpr
  intro v hv
  rw [joint_injection_dot]
  exact (annih_mem u (S i)).mp hu _ (hv i)

theorem joint_diagonal_injection (W : B→Mat D D) (i : B) (u : Vec D) :
    blockDiagonal W*ᵥ(jointInjection i u)=jointInjection i (W i*ᵥu) := by
  funext ⟨d,b⟩
  have he:=congrFun (joint_diagonal_mulVec W (jointInjection i u) b) d
  change (blockDiagonal W*ᵥjointInjection i u) (d,b)=
    (W b*ᵥjointProjection b (jointInjection i u)) d at he
  change (blockDiagonal W*ᵥjointInjection i u) (d,b)=if b=i then (W i*ᵥu) d else 0
  rw [he,joint_projection_injection]
  by_cases hi : b=i
  · simp only [hi,ite_true]
  · simp only [hi,ite_false,Matrix.mulVec_zero,Pi.zero_apply]

/-- A block-diagonal residual needs kernel separation only for pin
directions supported at one endpoint. Shared pinned ambient vectors may
give mixed-endpoint kernel vectors, and these are explicitly allowed. -/
theorem joint_block_kernel_residual (S L : B→Space (Vec D))
    (K : Space (Vec (D×B))) (hKS : K≤jointSpace S)
    (hK : ∀ i,Disjoint K ((S i⊓L i).map (jointInjection i)))
    (W : B→Mat D D)
    (hW : blockDiagonal W∈quadraticSquares (jointSpace S)⊔quadraticCross K)
    (hcol : ∀ i,colSp (W i)≤L i) :
    blockDiagonal W∈quadraticSquares (jointSpace (fun i=>S i⊓L i)) := by
  classical
  obtain ⟨M,hM,Z,hZ,he⟩:=Submodule.mem_sup.mp hW
  obtain ⟨T,hT,hZeq⟩:=quadraticCross_decompose hZ
  have hDecomp : blockDiagonal W=M+T+Tᵀ:=by rw [←he,hZeq]; abel
  have kill {P Q : Space (Vec (D×B))} {V : Mat (D×B) (D×B)} :
      V∈box P Q↔(∀ x∈annih P,Vᵀ*ᵥx=0) ∧ (∀ x∈annih Q,V*ᵥx=0) := by
    simpa only [annih_annih] using (box_kill (S:=annih P) (T:=annih Q) (M:=V))
  have hTT : Tᵀ∈box ⊤ (jointSpace S):=
    (box_mem ..).mpr ⟨le_top,by simpa using hT.trans hKS⟩
  have hz (i : B) (u : Vec D) (hu : u∈annih (S i)) : W i*ᵥu=0 := by
    let x:=jointInjection i u
    have hx : x∈annih (jointSpace S):=joint_injection_annih S i hu
    have hMx:=((kill.mp (quadraticSquares_data hM).2).2 x hx)
    have hTx:=((kill.mp hTT).2 x hx)
    have hEq : blockDiagonal W*ᵥx=T*ᵥx:=by
      rw [hDecomp,Matrix.add_mulVec,Matrix.add_mulVec,hMx,hTx,zero_add,add_zero]
    have hWK : blockDiagonal W*ᵥx∈K:=hEq.symm ▸ hT ⟨x,rfl⟩
    have hWS : W i*ᵥu∈S i:=by
      have hh:=hKS hWK i
      rw [show x=jointInjection i u from rfl,joint_diagonal_injection,
        joint_projection_injection,if_pos rfl] at hh
      exact hh
    have hWL : W i*ᵥu∈L i:=hcol i ⟨u,rfl⟩
    have hWP : blockDiagonal W*ᵥx∈(S i⊓L i).map (jointInjection i):=
      ⟨W i*ᵥu,⟨hWS,hWL⟩,(joint_diagonal_injection W i u).symm⟩
    have hzero : blockDiagonal W*ᵥx=0:=(hK i).le_bot ⟨hWK,hWP⟩
    have hh:=congrArg (jointProjection i) hzero
    rw [show x=jointInjection i u from rfl,joint_diagonal_injection,
      joint_projection_injection,if_pos rfl,map_zero] at hh
    exact hh
  have htop : blockDiagonal W∈quadraticSquares (⊤ : Space (Vec (D×B))):=
    quadratic_constraints_top_squares _ _ hW
  have hcols (i : B) : colSp (W i)≤S i⊓L i:=by
    have hs : (W i)ᵀ=W i:=by
      have hh:=quadraticSquares_data (joint_block_squares htop i)
      simpa only [joint_matrix_block_diagonal] using hh.1
    have hi : W i∈box (S i) (S i):=by
      have hh:=box_kill (S:=annih (S i)) (T:=annih (S i)) (M:=W i)
      rw [annih_annih] at hh
      exact hh.mpr ⟨by simpa only [hs] using hz i,hz i⟩
    exact le_inf ((box_mem ..).mp hi).1 (hcol i)
  exact quadraticSquares_project htop (joint_diagonal_columns _ W hcols)

end
end Lax793645Proofs.Simplifications
