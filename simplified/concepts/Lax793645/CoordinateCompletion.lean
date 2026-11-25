import Lax793645.ConstructionData

/-!
---
title: Completing a quadratic form in coordinates
type: lemma
---
A linear map given on a subspace extends into a hyperbolic space with prescribed
quadratic values and channel pairings. The frozen values and polar rows must be
compatible, including on the kernel. Rank factorization gives enough unused coordinate
pairs under the stated dimension bound.
-/

namespace Lax793645.CoordinateCompletion

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

axiom coordinate_quadratic_extension (h : ℕ) (M : Mat I I) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F] Hyperbolic h)
    (ell : Vec I→ₗ[F] C→ₗ[F] F)
    (hval : ∀ f : P,M.toQuadraticForm' f=hyperbolicQuadratic h (g₀ f))
    (hcompat : ∀ (f : P) (c : C),ell f c=(hyperbolicQuadratic h).polarBilin (g₀ f) c)
    (hrow : ∀ (f : P) (hf : g₀ f∈C) (v : Vec I),
      M.toQuadraticForm'.polarBilin f v=ell v ⟨g₀ f,hf⟩)
    (hroom : M.rank+5* dim C+6* dim P+2≤ h) :
    ∃ g : Vec I→ₗ[F] Hyperbolic h,
      (∀ v,hyperbolicQuadratic h (g v)=M.toQuadraticForm' v) ∧
      (∀ f : P,g f=g₀ f) ∧
      ∀ (v : Vec I) (c : C),(hyperbolicQuadratic h).polarBilin (g v) c=ell v c

end

end Lax793645.CoordinateCompletion
