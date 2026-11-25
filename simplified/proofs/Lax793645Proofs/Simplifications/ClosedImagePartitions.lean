import Lax793645Proofs.Simplifications.ClosedImagePeeling

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N c : ℕ}

structure ClosedImageCell (X : A→C→Mat (Fin N) I) (cl : ImageClosure C I c)
    (w r : Wgt A) (D ζ : ℝ) (K : ℕ) (S : Finset A) (a b : ImagePin C I N) : Prop where
  pos : 0<pr w (fun x=>x∈S)
  fixpin : ∀ x∈S,imagePinAgree X b x
  extendsSp : a.sp≤b.sp
  closed : cl.close b.sp=b.sp
  bound : imagePlanRank b.sp≤ imagePlanRank a.sp+K
  clear : imagePinClear X b ζ (onW w (fun x=>x∈S))
  density x : onW w (fun x=>x∈S) x≤bp ((D+K+1)*N)*r x

/-- A finite partition into closed, spreading image cells, with the
exceptional mass charged before any subsequent conditioning. -/
theorem closed_image_partition
    (X : A→C→Mat (Fin N) I) (hc : 1≤c) (cl : ImageClosure C I c)
    {r w : Wgt A} {D ζ : ℝ} (hz : 0<ζ) (hz' : ζ<1) (hn : 0<N)
    (hR : ∀ b : ImagePin C I N,cl.close b.sp=b.sp→
      pr r (imagePinAgree X b)≤fee N ((ζ/c)/4) (imagePlanRank b.sp))
    (hcap : ∀ x,w x≤bp (D*N)*r x) (hw : ∀ x,0≤w x)
    (R : Finset A) (a : ImagePin C I N) (ha : cl.close a.sp=a.sp)
    (hf : ∀ x∈R,imagePinAgree X a x)
    {K : ℕ} (hK : D+ζ≤((ζ/c)-(ζ/c)/4)*K) :
    ∃ G : Finset (Finset A),
      (∀ S∈G,S⊆R ∧ ∃ b,ClosedImageCell X cl w r D ζ K S a b) ∧
      (∀ x,∀ S∈G,∀ J∈G,x∈S→x∈J→S=J) ∧
      pr w (fun x=>x∈R ∧ ¬∃ S∈G,x∈S)≤bp (-ζ*N) := by
  classical
  induction R using Finset.strongInductionOn with | _ R ih
  by_cases hr : pr w (fun x=>x∈R)≤bp (-ζ*N)
  · exact ⟨∅,by simpa using hr⟩
  obtain ⟨S,b,hS,hpos,hfix,hext,hclosed,hbound,hclear,hdensity⟩:=
    closed_image_heavy_leaf X c hc cl hz hz' hn hR hcap hw R a ha hf hK (lt_of_not_ge hr)
  have hb : ClosedImageCell X cl w r D ζ K S a b:=
    ⟨hpos,hfix,hext,hclosed,hbound,hclear,hdensity⟩
  obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw hpos
  obtain ⟨G,hG,hU,hW⟩:=ih (R\S) (Finset.sdiff_ssubset hS ⟨x,hx⟩)
    (fun x h=>hf x (Finset.mem_sdiff.mp h).1)
  refine ⟨insert S G,fun J h=>?_,fun x J h J' h' g g'=>?_,?_⟩
  · rcases Finset.mem_insert.mp h with rfl|h
    · exact ⟨hS,b,hb⟩
    · exact ⟨(hG J h).1.trans Finset.sdiff_subset,(hG J h).2⟩
  · have hi (J) (h : J∈G) (g : x∈J) : x∉S:=
      (Finset.mem_sdiff.mp ((hG J h).1 g)).2
    rcases Finset.mem_insert.mp h with h|h <;> rcases Finset.mem_insert.mp h' with h'|h'
    · rw [h,h']
    · exact ((hi _ h' g') (h ▸ g)).elim
    · exact ((hi _ h g) (h' ▸ g')).elim
    · exact hU _ _ h _ h' g g'
  · refine (pr_mono hw ?_).trans hW
    intro x h
    simp only [Finset.exists_mem_insert,not_or] at h
    exact ⟨Finset.mem_sdiff.mpr ⟨h.1,h.2.1⟩,h.2.2⟩

end
end Lax793645Proofs.Simplifications
