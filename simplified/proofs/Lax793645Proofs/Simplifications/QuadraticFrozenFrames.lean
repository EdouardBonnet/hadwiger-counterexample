import Lax793645Proofs.Simplifications.RelativeQuadraticExtension
import Lax793645Proofs.Simplifications.QuadraticFrameMoves

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

/-- Complete frozen ambient images without creating any extra kernel.
Unlike rank-compressed channel extension, this preserves injectivity on
every subspace disjoint from the already forced identifications. -/
theorem quadratic_frozen_embedding [FiniteDimensional QField B] [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (hnd : q.polarBilin.Nondegenerate)
    (S : Submodule QField B) (g₀ : S→ₗ[QField]H)
    (hq : ∀ s : S,Q s=q (g₀ s))
    (hrow : ∀ s : S,g₀ s=0→∀ b,Q.polarBilin s b=0)
    (hroom : 2*Module.finrank QField B+2≤Module.finrank QField H) :
    ∃ g : B→ₗ[QField]H,(∀ b,q (g b)=Q b) ∧ (∀ s : S,g s=g₀ s) ∧
      g.ker=g₀.ker.map S.subtype := by
  classical
  let N:=g₀.ker.map S.subtype
  have hN : N≤Q.radical := by
    rintro b ⟨s,hs,rfl⟩
    have hs0 : g₀ s=0:=hs
    have hqs : Q s=0:=by rw [hq,hs0,map_zero]
    apply QuadraticMap.mem_radical_iff'.mpr
    refine ⟨hqs,?_⟩
    intro b
    change Q ((s:B)+b)=Q b
    rw [QuadraticMap.map_add Q,←QuadraticMap.polarBilin_apply_apply,hrow s hs0 b,hqs]
    simp
  obtain ⟨Q',hQ'⟩:=QuadraticMap.le_radical_iff.mp hN
  let p:=N.mkQ.comp S.subtype
  have hker (s : S) : p s=0↔g₀ s=0 := by
    change N.mkQ s=0↔g₀ s=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨v,hv,hvs⟩
      have he : v=s:=Subtype.ext hvs
      change g₀ v=0 at hv
      simpa only [he] using hv
    · intro hs
      exact ⟨s,hs,rfl⟩
  have hkle : p.ker≤g₀.ker:=fun s hs=>(hker s).mp hs
  let f : p.range→ₗ[QField]H:=
    (p.ker.liftQ g₀ hkle).comp p.quotKerEquivRange.symm.toLinearMap
  have hf (s : S) : f (p.rangeRestrict s)=g₀ s := by
    change p.ker.liftQ g₀ hkle (p.quotKerEquivRange.symm ⟨p s,_⟩)=g₀ s
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hfi : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    ext z
    simp only [LinearMap.mem_ker,Submodule.mem_bot]
    constructor
    · intro hz
      obtain ⟨s,hs⟩:=z.property
      have he : z=p.rangeRestrict s:=Subtype.ext hs.symm
      rw [he,hf] at hz
      exact Subtype.ext (hs.symm.trans ((hker s).mpr hz))
    · rintro rfl
      exact map_zero f
  have hfq (z : p.range) : q (f z)=Q' z := by
    obtain ⟨s,hs⟩:=z.property
    have he : z=p.rangeRestrict s:=Subtype.ext hs.symm
    rw [he,hf,←hq]
    exact (congrArg (fun A : QuadraticForm QField B=>A s) hQ').symm
  have hd : Module.finrank QField (B⧸N)≤Module.finrank QField B := by
    have hh:=N.finrank_quotient_add_finrank
    omega
  obtain ⟨j,hji,hjq,hjf⟩:=quadratic_embedding_extension Q' q hnd
    ((Nat.add_le_add_right (Nat.mul_le_mul_left 2 hd) 2).trans hroom) p.range f hfi hfq
  let g:=j.comp N.mkQ
  refine ⟨g,?_,?_,?_⟩
  · intro b
    exact (hjq (N.mkQ b)).trans (congrArg (fun A : QuadraticForm QField B=>A b) hQ')
  · intro s
    exact (hjf (p.rangeRestrict s)).trans (hf s)
  · ext b
    change j (N.mkQ b)=0↔b∈N
    constructor
    · intro hb
      exact (Submodule.Quotient.mk_eq_zero N).mp (hji (hb.trans (map_zero j).symm))
    · intro hb
      have hz : N.mkQ b=0:=(Submodule.Quotient.mk_eq_zero N).mpr hb
      rw [hz,map_zero]

theorem frozen_embedding_injective_on {g : B→ₗ[QField]H} {N T : Submodule QField B}
    (hker : g.ker=N) (hTN : Disjoint T N) : Function.Injective (g.comp T.subtype) := by
  apply (LinearMap.ker_eq_bot).mp
  ext v
  simp only [LinearMap.mem_ker,Submodule.mem_bot]
  constructor
  · intro hv
    apply Subtype.ext
    exact hTN.le_bot ⟨v.property,hker ▸ hv⟩
  · rintro rfl
    exact map_zero _

end
end Lax793645Proofs.Simplifications
