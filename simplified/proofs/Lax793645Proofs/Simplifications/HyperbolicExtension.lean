import Lax793645Proofs.Simplifications.RelativeQuadraticExtension
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

abbrev Hyperbolic (h : ℕ) := (Fin h→QField)×(Fin h→QField)

def hyperbolicQuadratic (h : ℕ) : QuadraticForm QField (Hyperbolic h) :=
  LinearMap.BilinMap.toQuadraticMap
    ((dotProductBilin QField QField : (Fin h→QField)→ₗ[QField]
      (Fin h→QField)→ₗ[QField] QField).compl₁₂
      (LinearMap.fst QField _ _) (LinearMap.snd QField _ _))

theorem hyperbolic_apply (h : ℕ) (v : Hyperbolic h) :
    hyperbolicQuadratic h v=dotProduct v.1 v.2 := rfl

theorem hyperbolic_polar (h : ℕ) (v w : Hyperbolic h) :
    (hyperbolicQuadratic h).polarBilin v w=dotProduct v.1 w.2+dotProduct w.1 v.2 := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  simp only [hyperbolic_apply,Prod.fst_add,Prod.snd_add,add_dotProduct,dotProduct_add]
  ring

theorem hyperbolic_nondegenerate (h : ℕ) :
    (hyperbolicQuadratic h).polarBilin.Nondegenerate := by
  constructor
  · intro v hv
    apply Prod.ext
    · funext i
      have hi := hv (0,Pi.single i 1)
      change (hyperbolicQuadratic h).polarBilin v (0,Pi.single i 1)=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi
    · funext i
      have hi := hv (Pi.single i 1,0)
      change (hyperbolicQuadratic h).polarBilin v (Pi.single i 1,0)=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi
  · intro v hv
    apply Prod.ext
    · funext i
      have hi := hv (0,Pi.single i 1)
      change (hyperbolicQuadratic h).polarBilin (0,Pi.single i 1) v=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi
    · funext i
      have hi := hv (Pi.single i 1,0)
      change (hyperbolicQuadratic h).polarBilin (Pi.single i 1,0) v=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi

/-- The proposed relative extension theorem with its exact channel budget. -/
theorem hyperbolic_relative_extension {B : Type} [AddCommGroup B] [Module QField B]
    [FiniteDimensional QField B] (h : ℕ)
    (Q : QuadraticForm QField B) (S : Submodule QField B)
    (C : Submodule QField (Hyperbolic h)) (g₀ : S→ₗ[QField] Hyperbolic h)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hQ : ∀ f : S,Q f=hyperbolicQuadratic h (g₀ f))
    (hell : ∀ (f : S) (c : C),ell f c=(hyperbolicQuadratic h).polarBilin (g₀ f) c)
    (hrow : ∀ (f : S) (hf : g₀ f∈C) (b : B),Q.polarBilin f b=ell b ⟨g₀ f,hf⟩)
    (hroom : Module.finrank QField Q.polarBilin.range+
      3*Module.finrank QField C+Module.finrank QField S+2≤h) :
    ∃ g : B→ₗ[QField] Hyperbolic h,(∀ b,hyperbolicQuadratic h (g b)=Q b) ∧
      (∀ f : S,g f=g₀ f) ∧
      ∀ (b : B) (c : C),(hyperbolicQuadratic h).polarBilin (g b) c=ell b c := by
  apply relative_quadratic_extension Q (hyperbolicQuadratic h)
    (hyperbolic_nondegenerate h) S C g₀ ell hQ hell hrow
  have hd : Module.finrank QField (Hyperbolic h)=2*h := by
    simp [Hyperbolic,Module.finrank_prod,two_mul]
  rw [hd]
  omega

end
end Lax793645Proofs.Simplifications
