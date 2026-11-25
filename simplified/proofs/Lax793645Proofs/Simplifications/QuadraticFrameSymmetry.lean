import Lax793645Proofs.Simplifications.QuadraticColumnCounts
import Lax793645Proofs.Simplifications.QuadraticEmbedding
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section

variable {D V : Type} [AddCommGroup D] [Module F D] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- Complete two frames with identical Gram data to matching ambient bases.
Equal counts of independent next columns suffice even at the last step. -/
theorem quadratic_frame_symmetry (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    (P Q : D →ₗ[F] V) (hP : Injective P) (hQ : Injective Q) (hform : ∀ d, q (P d) = q (Q d)) :
    ∃ e : q.IsometryEquiv q, ∀ d, e (P d) = Q d := by
  classical
  let _ : Finite V := Module.finite_of_finite F
  let _ : Fintype V := Fintype.ofFinite V
  let E := LinearEquiv.ofInjective P hP
  have hE (d : D) : (E d : V) = P d := rfl
  let i := Q.comp E.symm.toLinearMap
  have hi (s : P.range) : q (i s) = q s := by
    obtain ⟨d,rfl⟩ := E.surjective s
    simpa [i,hE] using (hform d).symm
  obtain ⟨g,hg,hgq,hgi⟩ := quadratic_extend_by_steps q q (S:=P.range) (g₀:=i)
    (hinj:=hQ.comp E.symm.injective) (hq:=hi) (by
      intro S j hj hjq x hx
      have hout : x ∉ S.subtype.range := by simpa using hx
      obtain ⟨y,hy,hyq,hpair⟩ := quadratic_column_partner q hq S.subtype j
        S.injective_subtype hj (fun s => (hjq s).symm) x hout
      apply quadratic_extend_column q q S j hj hjq x hx y hy hyq
      intro s
      have h := LinearMap.congr_fun hpair s
      change q.polarBilin y (j s) = q.polarBilin x (s:V) at h
      simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h)
  let e : q.IsometryEquiv q :=
    { LinearEquiv.ofBijective g ⟨hg, g.injective_iff_surjective.mp hg⟩ with map_app' := hgq }
  refine ⟨e,fun d => ?_⟩
  change g (P d) = Q d
  simpa only [i, hE, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using hgi (E d)

theorem quadratic_point_symmetry (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    {t z : V} (ht : t ≠ 0) (hz : z ≠ 0) (hval : q t = q z) :
    ∃ e : q.IsometryEquiv q, e t = z := by
  have inj (v : V) (hv : v ≠ 0) : Injective (toSpanSingleton F V v) := by
    apply LinearMap.ker_eq_bot.mp
    exact le_antisymm (fun a ha => (smul_eq_zero.mp ha).resolve_right hv) bot_le
  obtain ⟨e,he⟩ := quadratic_frame_symmetry q hq _ _ (inj t ht) (inj z hz) (fun a => by
    simp only [toSpanSingleton_apply, QuadraticMap.map_smul, hval])
  exact ⟨e,by simpa only [toSpanSingleton_apply_one] using he 1⟩

end
end Lax793645Proofs.Simplifications
