import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CoverSpaces

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
noncomputable section
variable {I : Type} [Fintype I]

/-- The kernel-cross correction cannot leave the frozen square while its
columns stay in a protected space disjoint from the kernel directions. -/
theorem quadratic_kernel_residual {S K L : Space (Vec I)} {W M T : Mat I I}
    (hKS : K ≤ S) (hKL : Disjoint K L) (hM : M ∈ box S S)
    (hT : colSp T ≤ K) (hW : colSp W ≤ L) (hsym : Wᵀ=W)
    (he : W=M+T+Tᵀ) : W∈box (S⊓L) (S⊓L) := by
  classical
  have kill {S T : Space (Vec I)} {M : Mat I I} :
      M∈box S T ↔ (∀ x∈annih S,Mᵀ*ᵥx=0) ∧ (∀ x∈annih T,M*ᵥx=0) := by
    simpa only [annih_annih] using (box_kill (S:=annih S) (T:=annih T) (M:=M))
  have hTT : Tᵀ ∈ box ⊤ S := (box_mem ..).mpr ⟨le_top,by simpa using hT.trans hKS⟩
  have hz (x : Vec I) (hx : x∈annih S) : W*ᵥx=0 := by
    have hMx := ((kill.mp hM).2 x hx)
    have hTx := ((kill.mp hTT).2 x hx)
    have hEq : W*ᵥx=T*ᵥx := by rw [he,Matrix.add_mulVec,Matrix.add_mulVec,hMx,hTx,zero_add,add_zero]
    have hK : W*ᵥx∈K := hEq.symm ▸ hT (show T*ᵥx∈colSp T from ⟨x,rfl⟩)
    exact hKL.le_bot ⟨hK,hW ⟨x,rfl⟩⟩
  have hWS : W∈box S S := kill.mpr ⟨by simpa only [hsym] using hz,hz⟩
  exact (box_mem ..).mpr ⟨le_inf ((box_mem ..).mp hWS).1 hW,
    le_inf ((box_mem ..).mp hWS).2 (by simpa only [hsym] using hW)⟩

/-- Squares in a subspace, over the binary field. -/
def quadraticSquares (S : Space (Vec I)) : Space (Mat I I) :=
  Submodule.span F {W | ∃ x∈S,W=vecMulVec x x}

def quadraticCross (K : Space (Vec I)) : Space (Mat I I) :=
  Submodule.span F {W | ∃ k∈K,∃ b,W=vecMulVec k b+vecMulVec b k}

theorem quadraticSquares_data {S : Space (Vec I)} {W : Mat I I}
    (hw : W∈quadraticSquares S) : Wᵀ=W ∧ W∈box S S := by
  induction hw using Submodule.span_induction with
  | mem W h =>
    obtain ⟨x,hx,rfl⟩ := h
    exact ⟨transpose_vecMulVec ..,outer_in_box x x hx hx⟩
  | zero => exact ⟨by simp,(box S S).zero_mem⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [transpose_add,hx.1,hy.1],(box S S).add_mem hx.2 hy.2⟩
  | smul c x _ hx =>
    exact ⟨by rw [transpose_smul,hx.1],(box S S).smul_mem c hx.2⟩

theorem quadraticCross_decompose {K : Space (Vec I)} {W : Mat I I}
    (hw : W∈quadraticCross K) : ∃ T,colSp T≤K ∧ W=T+Tᵀ := by
  induction hw using Submodule.span_induction with
  | mem W h =>
    obtain ⟨k,hk,b,rfl⟩ := h
    exact ⟨vecMulVec k b,((box_mem ..).mp (outer_in_box k b hk (Submodule.mem_top))).1,
      by rw [transpose_vecMulVec]⟩
  | zero => exact ⟨0,by simp [colSp],by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A,hA,rfl⟩ := hx
    obtain ⟨B,hB,rfl⟩ := hy
    refine ⟨A+B,?_,by rw [transpose_add]; abel⟩
    rintro _ ⟨v,rfl⟩
    change (A+B)*ᵥv∈K
    rw [Matrix.add_mulVec]
    exact K.add_mem (hA ⟨v,rfl⟩) (hB ⟨v,rfl⟩)
  | smul c x _ hx =>
    obtain ⟨A,hA,rfl⟩ := hx
    refine ⟨c•A,?_,by rw [transpose_smul,smul_add]⟩
    rintro _ ⟨v,rfl⟩
    change (c•A)*ᵥv∈K
    rw [Matrix.smul_mulVec]
    exact K.smul_mem c (hA ⟨v,rfl⟩)

theorem quadraticSquares_project {S T : Space (Vec I)} {W : Mat I I}
    (hw : W∈quadraticSquares S) (hc : colSp W≤T) : W∈quadraticSquares T := by
  classical
  have hs := (quadraticSquares_data hw).1
  have hl : prj T*W=W := by
    apply coe_mv_inj
    exact LinearMap.ext fun x => (by
      change (prj T*W)*ᵥx=W*ᵥx
      rw [←Matrix.mulVec_mulVec]
      exact (prj_data T).fixes _ (hc ⟨x,rfl⟩))
  have hr : W*(prj T)ᵀ=W := by
    simpa only [transpose_mul,hs] using congrArg Matrix.transpose hl
  have he : liftM (prj T) (prj T) W=W := by rw [liftM_def,hl,hr]
  rw [←he]
  clear he hr hl hs hc
  induction hw using Submodule.span_induction with
  | mem W h =>
    obtain ⟨x,hx,rfl⟩ := h
    rw [liftM_outer]
    exact Submodule.subset_span ⟨_,(prj_data T).onto x,rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (quadraticSquares T).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using (quadraticSquares T).smul_mem c hx

/-- Pro's kernel-cross intersection identity, without any independence
assumption on the frozen map. -/
theorem quadratic_kernel_intersection (S K L : Space (Vec I))
    (hKS : K≤S) (hKL : Disjoint K L) :
    (quadraticSquares S ⊔ quadraticCross K) ⊓ quadraticSquares L =
      quadraticSquares (S⊓L) := by
  classical
  apply le_antisymm
  · rintro W ⟨hW,hWL⟩
    obtain ⟨M,hM,Z,hZ,hEq⟩ := Submodule.mem_sup.mp hW
    obtain ⟨T,hT,hTeq⟩ := quadraticCross_decompose hZ
    have hL := quadraticSquares_data hWL
    have hF := quadratic_kernel_residual hKS hKL (quadraticSquares_data hM).2 hT
      ((box_mem ..).mp hL.2).1 hL.1 (by rw [←hEq,hTeq]; abel)
    exact quadraticSquares_project hWL ((box_mem ..).mp hF).1
  · apply le_inf
    · apply le_trans ?_ le_sup_left
      exact Submodule.span_mono (by rintro W ⟨x,hx,rfl⟩; exact ⟨x,hx.1,rfl⟩)
    · exact Submodule.span_mono (by rintro W ⟨x,hx,rfl⟩; exact ⟨x,hx.2,rfl⟩)
end
end Lax793645Proofs.Simplifications
