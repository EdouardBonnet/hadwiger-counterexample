import Lax793645Proofs.Simplifications.QuadraticFrozenFrames

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B H : Type} [AddCommGroup A] [Module QField A]
  [AddCommGroup B] [Module QField B] [AddCommGroup H] [Module QField H]

/-- The cross table specifies the polar pairings of two quadratic frames. -/
def pairedQuadratic (Q : QuadraticForm QField A) (R : QuadraticForm QField B)
    (T : A→ₗ[QField]B→ₗ[QField]QField) : QuadraticForm QField (A×B) :=
  Q.comp (LinearMap.fst QField A B)+R.comp (LinearMap.snd QField A B)+
    LinearMap.BilinMap.toQuadraticMap
      (T.compl₁₂ (LinearMap.fst QField A B) (LinearMap.snd QField A B))

theorem paired_quadratic_apply (Q : QuadraticForm QField A) (R : QuadraticForm QField B)
    (T : A→ₗ[QField]B→ₗ[QField]QField) (a : A) (b : B) :
    pairedQuadratic Q R T (a,b)=Q a+R b+T a b := rfl

theorem paired_quadratic_cross (Q : QuadraticForm QField A) (R : QuadraticForm QField B)
    (T : A→ₗ[QField]B→ₗ[QField]QField) (a : A) (b : B) :
    (pairedQuadratic Q R T).polarBilin (a,0) (0,b)=T a b := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    Prod.mk_add_mk,add_zero,zero_add,paired_quadratic_apply,map_zero,LinearMap.zero_apply]
  ring

/-- Realize a reciprocal cross table by two injective quadratic frames,
retaining all prescribed joint pin and key images. Only the identifications
forced by the frozen images are permitted. -/
theorem quadratic_pair_completion [FiniteDimensional QField A]
    [FiniteDimensional QField B] [FiniteDimensional QField H]
    (Q : QuadraticForm QField A) (R : QuadraticForm QField B)
    (T : A→ₗ[QField]B→ₗ[QField]QField) (q : QuadraticForm QField H)
    (hnd : q.polarBilin.Nondegenerate)
    (S : Submodule QField (A×B)) (g₀ : S→ₗ[QField]H)
    (hq : ∀ s : S,pairedQuadratic Q R T s=q (g₀ s))
    (hrow : ∀ s : S,g₀ s=0→∀ v,(pairedQuadratic Q R T).polarBilin s v=0)
    (hleft : ∀ a : A,(a,0)∈g₀.ker.map S.subtype→a=0)
    (hright : ∀ b : B,(0,b)∈g₀.ker.map S.subtype→b=0)
    (hroom : 2*(Module.finrank QField A+Module.finrank QField B)+2≤Module.finrank QField H) :
    ∃ (P : A→ₗ[QField]H) (U : B→ₗ[QField]H),
      Function.Injective P ∧ Function.Injective U ∧
      (∀ a,q (P a)=Q a) ∧ (∀ b,q (U b)=R b) ∧
      (∀ a b,q.polarBilin (P a) (U b)=T a b) ∧
      (∀ s : S,P s.val.1+U s.val.2=g₀ s) ∧
      ∀ a b,P a+U b=0↔(a,b)∈g₀.ker.map S.subtype := by
  obtain ⟨g,hgq,hgf,hgk⟩:=quadratic_frozen_embedding (pairedQuadratic Q R T) q hnd S g₀ hq hrow
    (by simpa only [Module.finrank_prod] using hroom)
  let P:=g.comp (LinearMap.inl QField A B)
  let U:=g.comp (LinearMap.inr QField A B)
  have hsum (a : A) (b : B) : P a+U b=g (a,b) := by
    change g (a,0)+g (0,b)=g (a,b)
    rw [←map_add]
    simp
  have hzero (a : A) (b : B) : P a+U b=0↔(a,b)∈g₀.ker.map S.subtype := by
    rw [hsum]
    change (a,b)∈g.ker↔_
    rw [hgk]
  have hPi : Function.Injective P := by
    apply (LinearMap.ker_eq_bot).mp
    ext a
    simp only [LinearMap.mem_ker,Submodule.mem_bot]
    constructor
    · intro ha
      exact hleft a ((hzero a 0).mp (by rw [map_zero,add_zero]; exact ha))
    · rintro rfl; exact map_zero _
  have hUi : Function.Injective U := by
    apply (LinearMap.ker_eq_bot).mp
    ext b
    simp only [LinearMap.mem_ker,Submodule.mem_bot]
    constructor
    · intro hb
      exact hright b ((hzero 0 b).mp (by rw [map_zero,zero_add]; exact hb))
    · rintro rfl; exact map_zero _
  have hPq (a : A) : q (P a)=Q a := by
    change q (g (a,0))=Q a
    simpa only [paired_quadratic_apply,map_zero,LinearMap.zero_apply,add_zero] using hgq (a,0)
  have hUq (b : B) : q (U b)=R b := by
    change q (g (0,b))=R b
    simpa only [paired_quadratic_apply,map_zero,LinearMap.zero_apply,zero_add,add_zero] using hgq (0,b)
  refine ⟨P,U,hPi,hUi,hPq,hUq,?_,?_,hzero⟩
  · intro a b
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hsum,hgq,
      paired_quadratic_apply,hPq,hUq]
    ring
  · intro s
    exact (hsum s.val.1 s.val.2).trans (hgf s)

end
end Lax793645Proofs.Simplifications
