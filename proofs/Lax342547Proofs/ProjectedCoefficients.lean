import Lax342547.ProjectedCoefficients
import Lax342547.TargetMatrices

namespace Lax342547Proofs.ProjectedCoefficients
open Lax342547.ProjectedCoefficients

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorAnnihilators

/--
---
conclusion: Lax342547.ProjectedCoefficients.exists_quotient_projection
---
-/
theorem exists_quotient_projection {I : Type} [Fintype I]
    (D : Submodule Binary (I → Binary)) :
    ∃ p : (I → Binary) →ₗ[Binary] (I → Binary),
      D.mkQ.comp p = D.mkQ ∧ LinearMap.ker p = D ∧ p.comp p = p := by
  obtain ⟨s, hs⟩ := D.mkQ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr D.mkQ_surjective)
  let p := s.comp D.mkQ
  have he : D.mkQ.comp p = D.mkQ := by
    dsimp [p]
    rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp]
  refine ⟨p, he, ?_, ?_⟩
  · apply le_antisymm
    · intro v hv
      rw [← Submodule.ker_mkQ D]
      change D.mkQ v = 0
      rw [← LinearMap.congr_fun he v]
      simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hv, map_zero]
    · intro v hv
      change s (D.mkQ v) = 0
      have hz : D.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
      rw [hz, map_zero]
  · dsimp [p]
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc D.mkQ s, hs,
      LinearMap.id_comp]

/--
---
conclusion: Lax342547.ProjectedCoefficients.projection_preserves_quotient_pairing
---
-/
theorem projection_preserves_quotient_pairing {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (p q : (I → Binary) →ₗ[Binary] (I → Binary))
    (hp : D.mkQ.comp p = D.mkQ) (hq : E.mkQ.comp q = E.mkQ) : by
      classical
      exact PureAnnihilates (C - p.toMatrix' * C * q.toMatrix'.transpose) D E := by
  classical
  intro β
  let F := β.compl₁₂ D.mkQ E.mkQ
  have hF : F.compl₁₂ p q = F := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change β (D.mkQ (p v)) (E.mkQ (q w)) = β (D.mkQ v) (E.mkQ w)
    have hpv := LinearMap.congr_fun hp v
    have hqw := LinearMap.congr_fun hq w
    change D.mkQ (p v) = D.mkQ v at hpv
    change E.mkQ (q w) = E.mkQ w at hqw
    rw [hpv, hqw]
  have hm : p.toMatrix'.transpose * (LinearMap.BilinForm.toMatrix' F) * q.toMatrix' = (LinearMap.BilinForm.toMatrix' F) := by
    have hm := LinearMap.BilinForm.toMatrix'_comp F p q
    change LinearMap.BilinForm.toMatrix' (F.compl₁₂ p q) = _ at hm
    rw [hF] at hm
    exact hm.symm
  unfold pureContraction
  rw [map_sub, Lax342547.TargetMatrices.sandwich_adjoint, hm, sub_self]

end Lax342547Proofs.ProjectedCoefficients
