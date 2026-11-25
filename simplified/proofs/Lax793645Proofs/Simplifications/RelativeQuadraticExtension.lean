import Lax793645Proofs.Simplifications.RelativeQuadraticCompression
import Lax793645Proofs.Simplifications.QuadraticEmbedding
import Mathlib.LinearAlgebra.Isomorphisms

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

theorem frozen_graph_kernel (S : Submodule QField B) (C : Submodule QField H)
    (g₀ : S→ₗ[QField] H) (f : S) (c : C) :
    ((f:B),c)∈frozenKernel S C g₀ ↔ g₀ f+(c:H)=0 := by
  constructor
  · rintro ⟨v,hv⟩
    have hf : v.val=f := Subtype.ext (congrArg Prod.fst hv)
    have hc : g₀ v.val=(c:H) := congrArg (fun z : B×C=>(z.2:H)) hv
    rw [hf] at hc
    rw [←hc]
    exact ZModModule.add_self _
  · intro hh
    have hc : (c:H)=g₀ f := add_left_cancel (hh.trans (ZModModule.add_self _).symm)
    have hfC : g₀ f∈C := hc ▸ c.property
    refine ⟨⟨f,hfC⟩,?_⟩
    apply Prod.ext
    · rfl
    · exact Subtype.ext hc.symm

/-- Relative quadratic extension with arbitrary frozen kernel. The room
bound specializes to Pro's stated channel bound in a hyperbolic space. -/
theorem relative_quadratic_extension [FiniteDimensional QField B] [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (hnd : q.polarBilin.Nondegenerate)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=q (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),Q.polarBilin f b=ell b ⟨g₀ f,hf⟩)
    (hroom : 2*(Module.finrank QField Q.polarBilin.range+
      3*Module.finrank QField C+Module.finrank QField S+2)≤Module.finrank QField H) :
    ∃ g : B→ₗ[QField] H,(∀ b,q (g b)=Q b) ∧ (∀ f : S,g f=g₀ f) ∧
      ∀ (b : B) (c : C),q.polarBilin (g b) c=ell b c := by
  classical
  obtain ⟨N,Q',hQ',hNF,hdim⟩ := bounded_relative_quotient Q q S C g₀ ell hQ hell hrow
  let lift : S×C→ₗ[QField] B×C := S.subtype.prodMap (LinearMap.id : C→ₗ[QField] C)
  let p : S×C→ₗ[QField] (B×C)⧸N := N.mkQ.comp lift
  let a : S×C→ₗ[QField] H :=
    g₀.comp (LinearMap.fst QField S C)+C.subtype.comp (LinearMap.snd QField S C)
  have hker (z : S×C) : p z=0 ↔ a z=0 := by
    change N.mkQ (lift z)=0 ↔ g₀ z.1+(z.2:H)=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    have hzF : lift z∈frozenSubspace S C := ⟨z,rfl⟩
    have hzN : lift z∈N ↔ lift z∈frozenKernel S C g₀ := by
      rw [←hNF]
      exact ⟨fun h=>⟨h,hzF⟩,fun h=>h.1⟩
    rw [hzN]
    exact frozen_graph_kernel S C g₀ z.1 z.2
  have hkle : p.ker≤a.ker := fun z hz=>(hker z).mp hz
  let f : p.range→ₗ[QField] H :=
    (p.ker.liftQ a hkle).comp p.quotKerEquivRange.symm.toLinearMap
  have hf (z : S×C) : f (p.rangeRestrict z)=a z := by
    change p.ker.liftQ a hkle (p.quotKerEquivRange.symm ⟨p z,_⟩)=a z
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hfi : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    ext z
    simp only [LinearMap.mem_ker,Submodule.mem_bot]
    constructor
    · intro hz
      obtain ⟨w,hw⟩ := z.property
      have hzw : z=p.rangeRestrict w := Subtype.ext hw.symm
      rw [hzw,hf] at hz
      apply Subtype.ext
      exact hw.symm.trans ((hker w).mpr hz)
    · rintro rfl
      exact map_zero f
  have hfq (z : p.range) : q (f z)=Q' z := by
    obtain ⟨w,hw⟩ := z.property
    have hzw : z=p.rangeRestrict w := Subtype.ext hw.symm
    rw [hzw,hf]
    have hval := congrArg (fun r : QuadraticForm QField (B×C)=>r (lift w)) hQ'
    change Q' (p w)=Q w.1+q w.2+ell w.1 w.2 at hval
    change q (a w)=Q' (p w)
    rw [hval,hQ,hell]
    change q (g₀ w.1+(w.2:H))=q (g₀ w.1)+q w.2+q.polarBilin (g₀ w.1) w.2
    exact QuadraticMap.map_add q _ _
  obtain ⟨j,hji,hjq,hjf⟩ := quadratic_embedding_extension Q' q hnd
    (by dsimp only [QField] at *; omega) p.range f hfi hfq
  let G : B×C→ₗ[QField] H := j.comp N.mkQ
  have hGf (z : S×C) : G (lift z)=a z := (hjf (p.rangeRestrict z)).trans (hf z)
  have hGq (z : B×C) : q (G z)=augmentedQuadratic Q q C ell z := by
    exact (hjq (N.mkQ z)).trans (congrArg (fun r : QuadraticForm QField (B×C)=>r z) hQ')
  let g : B→ₗ[QField] H := G.comp (LinearMap.inl QField B C)
  have hGc (c : C) : G (0,c)=(c:H) := by
    simpa [lift,a] using hGf (0,c)
  refine ⟨g,?_,?_,?_⟩
  · intro b
    simpa [g,augmentedQuadratic_apply] using hGq (b,0)
  · intro f
    simpa [g,lift,a] using hGf (f,0)
  · intro b c
    have hc := hGq (b,c)
    have hb := hGq (b,0)
    have hsum : G (b,c)=g b+(c:H) := by
      change G (b,c)=G (b,0)+(c:H)
      rw [←hGc,←map_add]
      simp
    rw [hsum,QuadraticMap.map_add q] at hc
    have hbq : q (g b)=Q b := by simpa [g,augmentedQuadratic_apply] using hb
    rw [hbq] at hc
    change Q b+q c+q.polarBilin (g b) c=Q b+q c+ell b c at hc
    exact add_left_cancel hc

end
end Lax793645Proofs.Simplifications
