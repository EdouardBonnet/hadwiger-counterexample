import Lax793645Proofs.Simplifications.RelativeQuadraticRank

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

def frozenSubspace (S : Submodule QField B) (C : Submodule QField H) :
    Submodule QField (B×C) :=
  (S.subtype.prodMap (LinearMap.id : C→ₗ[QField] C)).range

theorem frozenKernel_le_frozenSubspace (S : Submodule QField B) (C : Submodule QField H)
    (g₀ : S→ₗ[QField] H) : frozenKernel S C g₀≤frozenSubspace S C := by
  rintro z ⟨f,rfl⟩
  exact ⟨(f.val,⟨g₀ f.val,f.property⟩),rfl⟩

/-- The exact dimension bound in the proposed relative extension argument.
The quotient identifies precisely the prescribed frozen kernel and no
additional frozen vectors. -/
theorem bounded_relative_quotient [FiniteDimensional QField B] [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=q (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),Q.polarBilin f b=ell b ⟨g₀ f,hf⟩) :
    ∃ (N : Submodule QField (B×C)) (Q' : QuadraticForm QField ((B×C)⧸N)),
      Q'.comp N.mkQ=augmentedQuadratic Q q C ell ∧
      N⊓frozenSubspace S C=frozenKernel S C g₀ ∧
      Module.finrank QField ((B×C)⧸N)≤Module.finrank QField Q.polarBilin.range+
        3*Module.finrank QField C+Module.finrank QField S+1 := by
  obtain ⟨N,hN,hNF,hbound⟩ := quadratic_compression_preserving_kernel
    (augmentedQuadratic Q q C ell) (frozenSubspace S C) (frozenKernel S C g₀)
      (frozenKernel_le_frozenSubspace S C g₀)
      (frozenKernel_le_radical Q q S C g₀ ell hQ hell hrow)
  obtain ⟨Q',hQ'⟩ := QuadraticMap.le_radical_iff.mp hN
  refine ⟨N,Q',hQ',hNF,?_⟩
  have hF : Module.finrank QField (frozenSubspace S C)≤
      Module.finrank QField S+Module.finrank QField C := by
    unfold frozenSubspace
    have h := LinearMap.finrank_range_le (R:=QField) (M:=S×C) (M':=B×C)
      (S.subtype.prodMap (LinearMap.id : C→ₗ[QField] C))
    simpa only [Module.finrank_prod] using h
  have hp := augmented_polar_rank Q q C ell
  dsimp only [QField] at *
  omega
end
end Lax793645Proofs.Simplifications
