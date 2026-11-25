import Mathlib.LinearAlgebra.Dual.Lemmas
import Lax793645Proofs.Simplifications.RelativeQuadraticKernel
import Lax793645Proofs.Simplifications.QuadraticRadicalCompression

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

theorem augmented_polar (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (C : Submodule QField H) (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (b b' : B) (c c' : C) :
    (augmentedQuadratic Q q C ell).polarBilin (b,c) (b',c')=
      Q.polarBilin b b'+q.polarBilin c c'+ell b c'+ell b' c := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  change (Q (b+b')+q ((c:H)+c')+ell (b+b') (c+c'))-
    (Q b+q c+ell b c)-(Q b'+q c'+ell b' c')=_
  simp only [map_add,LinearMap.add_apply]
  ring

theorem augmented_polar_rank [FiniteDimensional QField B] [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (C : Submodule QField H) (ell : B→ₗ[QField] C→ₗ[QField] QField) :
    Module.finrank QField (augmentedQuadratic Q q C ell).polarBilin.range ≤
      Module.finrank QField Q.polarBilin.range+2*Module.finrank QField C := by
  let A : B×C →ₗ[QField] Q.polarBilin.range×((C→ₗ[QField] QField)×C) :=
    ((Q.polarBilin.rangeRestrict.comp (LinearMap.fst QField B C))).prod
      ((ell.comp (LinearMap.fst QField B C)).prod (LinearMap.snd QField B C))
  have hk : A.ker≤(augmentedQuadratic Q q C ell).polarBilin.ker := by
    rintro ⟨b,c⟩ hx
    change A (b,c)=0 at hx
    have hc : c=0 := congrArg (fun z => z.2.2) hx
    have he : ell b=0 := congrArg (fun z => z.2.1) hx
    have hb : Q.polarBilin b=0 := congrArg (fun z => z.1.val) hx
    apply LinearMap.ext
    rintro ⟨b',c'⟩
    rw [augmented_polar,hb,hc,he]
    simp
  have h1 := LinearMap.finrank_range_add_finrank_ker (K:=QField) (V:=B×C)
    (V₂:=Q.polarBilin.range×((C→ₗ[QField] QField)×C)) A
  have h2 := (augmentedQuadratic Q q C ell).polarBilin.finrank_range_add_finrank_ker
  have hker := Submodule.finrank_mono hk
  have hr := Submodule.finrank_le A.range
  have hbound : Module.finrank QField A.range≤
      Module.finrank QField Q.polarBilin.range+2*Module.finrank QField C := by
    simpa only [Module.finrank_prod,Subspace.dual_finrank_eq, two_mul,add_assoc] using hr
  omega
end
end Lax793645Proofs.Simplifications
