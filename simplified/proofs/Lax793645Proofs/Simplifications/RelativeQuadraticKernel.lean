import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Lax793645Proofs.Simplifications
noncomputable section
abbrev QField := ZMod 2
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

/-- The augmented quadratic form used in relative extension. -/
def augmentedQuadratic (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (C : Submodule QField H) (ell : B →ₗ[QField] C →ₗ[QField] QField) :
    QuadraticForm QField (B×C) :=
  Q.comp (LinearMap.fst QField B C) +
  q.comp (C.subtype.comp (LinearMap.snd QField B C)) +
  LinearMap.BilinMap.toQuadraticMap
    (ell.compl₁₂ (LinearMap.fst QField B C) (LinearMap.snd QField B C))

theorem augmentedQuadratic_apply (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (C : Submodule QField H) (ell : B →ₗ[QField] C →ₗ[QField] QField) (b : B) (c : C) :
    augmentedQuadratic Q q C ell (b,c)=Q b+q c+ell b c := rfl

/-- The kernel-row compatibility is exactly what makes the frozen kernel
lie in the quadratic radical of the augmented form. -/
theorem augmented_kernel_radical (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=q (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),
      Q.polarBilin f b=ell b ⟨g₀ f,hf⟩)
    (f : S) (hf : g₀ f∈C) :
    ((f:B),(⟨g₀ f,hf⟩:C))∈(augmentedQuadratic Q q C ell).radical := by
  have h2 : (2:QField)=0 := by decide
  have hself (v : H) : q.polarBilin v v=0 := by
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,h2]
  apply QuadraticMap.mem_radical_iff'.mpr
  constructor
  · rw [augmentedQuadratic_apply,hQ,hell,hself]
    simp [CharTwo.add_self_eq_zero]
  · rintro ⟨b,c⟩
    change Q (f+b)+q (g₀ f+c)+ell (f+b) (⟨g₀ f,hf⟩+c)=Q b+q c+ell b c
    rw [QuadraticMap.map_add Q,QuadraticMap.map_add q]
    simp only [map_add,LinearMap.add_apply]
    rw [hQ,hell f ⟨g₀ f,hf⟩,hell f c,←QuadraticMap.polarBilin_apply_apply,
      ←QuadraticMap.polarBilin_apply_apply,hrow f hf,hself]
    ring_nf
    simp [h2]

/-- Graph of the frozen map on precisely those frozen vectors whose image
belongs to the prescribed channel subspace. -/
def frozenKernel (S : Submodule QField B) (C : Submodule QField H)
    (g₀ : S→ₗ[QField] H) : Submodule QField (B×C) :=
  LinearMap.range ({
    toFun := fun f : C.comap g₀ => ((f.val:B),(⟨g₀ f.val,f.property⟩:C))
    map_add' := by
      intro f k
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact g₀.map_add _ _
    map_smul' := by
      intro a f
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact g₀.map_smul a f.val
  } : C.comap g₀ →ₗ[QField] B×C)

theorem frozenKernel_le_radical (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=q (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),
      Q.polarBilin f b=ell b ⟨g₀ f,hf⟩) :
    frozenKernel S C g₀≤(augmentedQuadratic Q q C ell).radical := by
  rintro z ⟨f,rfl⟩
  exact augmented_kernel_radical Q q S C g₀ ell hQ hell hrow f.val f.property

/-- The augmented form descends through the frozen kernel, including when
the frozen map has a nontrivial kernel. -/
theorem relative_quadratic_quotient (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=q (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),
      Q.polarBilin f b=ell b ⟨g₀ f,hf⟩) :
    ∃ Q' : QuadraticForm QField ((B×C) ⧸ frozenKernel S C g₀),
      Q'.comp (frozenKernel S C g₀).mkQ=augmentedQuadratic Q q C ell :=
  QuadraticMap.le_radical_iff.mp (frozenKernel_le_radical Q q S C g₀ ell hQ hell hrow)

end
end Lax793645Proofs.Simplifications
