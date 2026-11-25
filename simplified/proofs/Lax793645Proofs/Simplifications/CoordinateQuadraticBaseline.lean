import Lax793645Proofs.Simplifications.RelativeQuadraticBaseline

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

/-- Solve the frozen values and all forced polar rows by linear equations.
The frozen map is allowed to have a kernel. -/
theorem coordinate_quadratic_baseline [FiniteDimensional QField B]
    [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (hnd : q.polarBilin.Nondegenerate)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=q (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),Q.polarBilin f b=ell b ⟨g₀ f,hf⟩) :
    ∃ g : B→ₗ[QField] H,(∀ f : S,g f=g₀ f) ∧
      (∀ (b : B) (c : C),q.polarBilin (g b) c=ell b c) ∧
      (∀ (b : B) (f : S),q.polarBilin (g b) (g₀ f)=Q.polarBilin b f) ∧
      Module.finrank QField g.range≤Module.finrank QField C+2*Module.finrank QField S := by
  let v : C×S→ₗ[QField] H :=
    C.subtype.comp (LinearMap.fst QField C S)+g₀.comp (LinearMap.snd QField C S)
  let T : B→ₗ[QField] (C×S)→ₗ[QField] QField :=
    (LinearMap.fst QField C S).dualMap.comp ell+
    (S.subtype.comp (LinearMap.snd QField C S)).dualMap.comp Q.polarBilin
  have hker (b : B) : v.ker≤(T b).ker := by
    rintro ⟨c,f⟩ hz
    change (c:H)+g₀ f=0 at hz
    have hcf : (c:H)=g₀ f := by
      exact add_right_cancel (hz.trans (ZModModule.add_self _).symm)
    have hf : g₀ f∈C := hcf ▸ c.property
    change ell b c+Q.polarBilin b f=0
    have hsym : Q.polarBilin b f=Q.polarBilin f b := by
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
      rw [add_comm b (f:B)]
      ring
    rw [hsym,hrow f hf b]
    have he : (⟨g₀ f,hf⟩:C)=c := Subtype.ext hcf.symm
    rw [he]
    exact ZModModule.add_self _
  obtain ⟨j,hj⟩ := v.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (fun y=>by
      obtain ⟨x,hx⟩ := y.property
      exact ⟨x,Subtype.ext hx⟩))
  let L : B→ₗ[QField] v.range→ₗ[QField] QField := j.dualMap.comp T
  have hL (b : B) (z : C×S) : L b (v.rangeRestrict z)=T b z := by
    have hv : v (j (v.rangeRestrict z))=v z :=
      congrArg Subtype.val (LinearMap.congr_fun hj (v.rangeRestrict z))
    have hz : j (v.rangeRestrict z)-z∈v.ker := by
      change v (j (v.rangeRestrict z)-z)=0
      rw [map_sub,hv,sub_self]
    have hh := hker b hz
    change T b (j (v.rangeRestrict z)-z)=0 at hh
    rw [map_sub,sub_eq_zero] at hh
    exact hh
  have hqq (f t : S) : Q.polarBilin (f:B) (t:B)=q.polarBilin (g₀ f) (g₀ t) := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    have hsum : Q ((f:B)+(t:B))=q (g₀ f+g₀ t) := by
      simpa only [map_add,Submodule.coe_add] using hQ (f+t)
    rw [hsum,hQ f,hQ t]
  have hcompat (f : S) (d : v.range) : L f d=q.polarBilin (g₀ f) d := by
    obtain ⟨z,hz⟩ := d.property
    have hd : d=v.rangeRestrict z := Subtype.ext hz.symm
    rw [hd,hL]
    change ell f z.1+Q.polarBilin f z.2=q.polarBilin (g₀ f) ((z.1:H)+g₀ z.2)
    rw [map_add,hell,hqq]
  obtain ⟨g,hg,hproj,hr⟩ := relative_quadratic_baseline q hnd S v.range g₀ L hcompat
  refine ⟨g,hg,?_,?_,?_⟩
  · intro b c
    have hh := (hproj b (v.rangeRestrict (c,0))).trans (hL b (c,0))
    simpa [v,T] using hh
  · intro b f
    have hh := (hproj b (v.rangeRestrict (0,f))).trans (hL b (0,f))
    simpa [v,T] using hh
  · have hv : Module.finrank QField v.range≤Module.finrank QField C+Module.finrank QField S := by
      simpa only [Module.finrank_prod] using LinearMap.finrank_range_le v
    omega

end
end Lax793645Proofs.Simplifications
