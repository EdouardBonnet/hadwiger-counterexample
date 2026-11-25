import Lax793645Proofs.Simplifications.ProtectedTensorAnnihilators
import Lax793645Proofs.Simplifications.QuadraticKernelIntersection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {D : Type} [Fintype D]

/-- The quadratic kernel constraints already imply the ordinary two-sided
quotient constraint. In particular their rank bound is twice dim F. -/
theorem quadratic_annihilator_vanish (P K : Space (Vec D)) (hK : K≤P)
    {w : Mat D D} (hw : w∈quadraticSquares P⊔quadraticCross K) : vanish P P w := by
  obtain ⟨M,hM,Z,hZ,rfl⟩:=Submodule.mem_sup.mp hw
  obtain ⟨T,hT,rfl⟩:=quadraticCross_decompose hZ
  have hc:=(box_mem ..).mp (quadraticSquares_data hM).2
  intro x hx y hy
  have kill (M : Mat D D) (h : colSp M≤P) (x y : Vec D) (hx : x∈annih P) :
      evmat M x y=0 := (annih_mem x P).mp hx _ (h ⟨y,rfl⟩)
  change evmat (M+(T+Tᵀ)) x y=0
  simp only [evmat,Matrix.add_mulVec,dotProduct_add]
  change evmat M x y+(evmat T x y+evmat Tᵀ x y)=0
  rw [kill M hc.1 x y hx,kill T (hT.trans hK) x y hx,evmat_transpose,
    kill T (hT.trans hK) y x hy]
  simp

theorem quadratic_annihilator_rank (P K : Space (Vec D)) (hK : K≤P)
    {w : Mat D D} (hw : w∈quadraticSquares P⊔quadraticCross K) :
    w.rank≤2*dim P := by
  simpa only [two_mul] using rank_vanish (quadratic_annihilator_vanish P K hK hw)

variable {S T I : Type} [Fintype S] [Fintype T] [Fintype I]

/-- This connects the affine-selector isolation theorem to the quadratic
kernel constraints. Its residual lies on the actual primal pins, without
any derivative response or independence of frozen channel images. -/
theorem quadratic_protected_annihilator
    (U : Space (Vec S)) (V : Space (Vec T)) (P K : Space (Vec (S×T)))
    (s : I→Vec S) (t : I→Vec T)
    (hs : LinearIndependent F (U.mkQ∘s)) (ht : LinearIndependent F (V.mkQ∘t))
    (εS : Vec S) (εT : Vec T) (hs1 : ∀ i,dotProduct εS (s i)=1)
    (ht1 : ∀ i,dotProduct εT (t i)=1)
    (hPL : P≤tensorCross U V)
    (hK : K≤P⊔selectedTensorSpace s t) (hKP : Disjoint K P)
    (R : ℕ) (hR : 2*dim (P⊔selectedTensorSpace s t : Space (Vec (S×T)))≤R)
    (hP : ∀ x∈P,Matrix.rank (flattenMatrix.symm x)≤R^2+Fintype.card I→
      x∈tensorRectangle U V)
    (w : Mat (S×T) (S×T)) (hw : w∈affineTensorSpace εS εT)
    (hquad : w∈quadraticSquares (P⊔selectedTensorSpace s t)⊔quadraticCross K) :
    ∃ (c : I→F) (z : Mat (S×T) (S×T)),
      w=(∑ i,c i•vecMulVec (tensorRay (s i) (t i)) (tensorRay (s i) (t i)))+z ∧
      z∈quadraticSquares P := by
  classical
  let A:=selectedTensorSpace s t
  let L:=tensorCross U V
  let F₀:=P⊔A
  have hAL : Disjoint A L:=selected_tensor_disjoint_cross U V s t hs ht
  have hFL : F₀⊓L=P := by
    apply le_antisymm
    · rintro x ⟨hx,hL⟩
      obtain ⟨p,hp,a,ha,he⟩:=Submodule.mem_sup.mp hx
      have hpa : p+a∈L:=he.symm ▸ hL
      have haL : a∈L:=by simpa using L.sub_mem hpa (hPL hp)
      have hz : a=0:=hAL.le_bot ⟨ha,haL⟩
      simpa [←he,hz] using hp
    · exact le_inf le_sup_left hPL
  have hKL : Disjoint K L := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hp : x∈P:=hFL ▸ (show x∈F₀⊓L from ⟨hK hx.1,hx.2⟩)
    exact hKP.le_bot ⟨hx.1,hp⟩
  obtain ⟨c,z,he,hz⟩:=protected_tensor_annihilator U V P P s t hs ht εS εT hs1 ht1
    R hP hP w hw ((quadratic_annihilator_rank _ _ hK hquad).trans hR)
    (quadratic_annihilator_vanish _ _ hK hquad)
  let a : Mat (S×T) (S×T):=∑ i,c i•vecMulVec (tensorRay (s i) (t i)) (tensorRay (s i) (t i))
  have ha : a∈quadraticSquares F₀ := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨tensorRay (s i) (t i),
      (show A≤F₀ from le_sup_right) (Submodule.subset_span ⟨i,rfl⟩),rfl⟩
  have hwa : z=w-a := by change w=a+z at he; rw [he]; abel
  have hzq : z∈quadraticSquares F₀⊔quadraticCross K := by
    rw [hwa]
    exact Submodule.sub_mem _ hquad
      ((show quadraticSquares F₀≤quadraticSquares F₀⊔quadraticCross K from le_sup_left) ha)
  have hsquares : affineTensorSpace εS εT≤quadraticSquares (⊤ : Space (Vec (S×T))) := by
    apply Submodule.span_le.mpr
    rintro M ⟨u,v,_,_,rfl⟩
    exact Submodule.subset_span ⟨tensorRay u v,Submodule.mem_top,rfl⟩
  have hatop : a∈quadraticSquares (⊤ : Space (Vec (S×T))) := by
    apply (Submodule.span_mono ?_) ha
    rintro M ⟨v,_,rfl⟩
    exact ⟨v,Submodule.mem_top,rfl⟩
  have hztop : z∈quadraticSquares (⊤ : Space (Vec (S×T))) := by
    rw [hwa]
    exact Submodule.sub_mem _ (hsquares hw) hatop
  have hzL : z∈quadraticSquares L:=quadraticSquares_project hztop ((box_mem ..).mp hz).1
  refine ⟨c,z,he,?_⟩
  have hh : z∈(quadraticSquares F₀⊔quadraticCross K)⊓quadraticSquares L:=⟨hzq,hzL⟩
  rwa [quadratic_kernel_intersection F₀ K L hK hKL,hFL] at hh

end
end Lax793645Proofs.Simplifications
