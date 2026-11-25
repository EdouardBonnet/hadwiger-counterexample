import Lax793645Proofs.Simplifications.QuadraticOrbitLaws
import Lax793645Proofs.Simplifications.QuadraticFrameCounts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B R V : Type} [AddCommGroup B] [Module F B]
  [AddCommGroup R] [Module F R] [FiniteDimensional F R]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

def quadraticPolarRead (q : QuadraticForm F V) (P : R→ₗ[F]V) :
    V→ₗ[F]Module.Dual F R:=P.dualMap.comp q.polarBilin

theorem quadratic_polar_read_surjective (q : QuadraticForm F V)
    (hq : q.polarBilin.Nondegenerate) (P : R→ₗ[F]V) (hP : Injective P) :
    Surjective (quadraticPolarRead q P) :=
  (LinearMap.dualMap_surjective_of_injective hP).comp
    (LinearMap.BilinForm.toDual q.polarBilin hq).surjective

variable [Fintype V] [Fintype (B→ₗ[F]V)] [Fintype (Module.Dual F R)]

/-- A fixed polar row has the same probability at any two nonzero
ambient vectors with the same quadratic value. -/
theorem quadratic_row_orbit (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    (C : QuadraticForm F B→Prop) (J : R→ₗ[F]B) (θ : Module.Dual F R)
    {t z : V} (ht : t≠0) (hz : z≠0) (hval : q t=q z)
    (hroom : 8≤dim V) :
    pr (unifOn (quadraticFramesAt q C)) (fun P=>quadraticPolarRead q (P.comp J) t=θ)=
      pr (unifOn (quadraticFramesAt q C)) (fun P=>quadraticPolarRead q (P.comp J) z=θ) := by
  obtain ⟨e,he⟩ := quadratic_point_symmetry q hq ht hz hval
  let E:=quadraticPost (B:=B) q e
  let w:=unifOn (quadraticFramesAt q C)
  have hw (P : B→ₗ[F]V) : w (E P)=w P := by
    simp only [w,E,unifOn_val,←quadratic_post_invar q e C]
  have hp (P : B→ₗ[F]V) : quadraticPolarRead q ((E P).comp J) z=
      quadraticPolarRead q (P.comp J) t := by
    apply LinearMap.ext
    intro r
    change q.polarBilin z (e (P (J r)))=q.polarBilin t (P (J r))
    rw [←he,quadratic_isometry_polar]
  have hh:=avg_bij E w (fun P=>ind (quadraticPolarRead q (P.comp J) z=θ))
  simpa only [hw,hp,pr] using hh

/-- The row restriction to an injective nominal subspace is bounded by
the inverse mass of its nonzero quadratic sphere, independently of the
dimension and detailed quadratic data of the full frame. -/
theorem quadratic_frame_row_cap (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    (C : QuadraticForm F B→Prop) (J : R→ₗ[F]B) (hJ : Injective J)
    (θ : Module.Dual F R) (t : V) (ht : t≠0) (hroom : 8≤dim V)
    {a : ℝ} (ha : 0<a) (hs : a≤pr unif (fun z : V=>z≠0 ∧ q z=q t)) :
    pr (unifOn (quadraticFramesAt q C)) (fun P=>quadraticPolarRead q (P.comp J) t=θ)≤
      a⁻¹*bp (-(dim R:ℝ)) := by
  classical
  let S:=fun z : V=>z≠0 ∧ q z=q t
  let w:=unifOn (quadraticFramesAt q C)
  let ν:=unifOn S
  have hν : IsLaw ν:=unifOn_law ⟨t,ht,rfl⟩
  have hv (z : V) : ν z≤a⁻¹*unif z:=by
    simpa only [on_unif] using on_mon unif_law.nz ha hs z
  have he : pr w (fun P=>quadraticPolarRead q (P.comp J) t=θ)=
      avg ν (fun z=>pr w (fun P=>quadraticPolarRead q (P.comp J) z=θ)) := by
    rw [←hν.avg_const (pr w (fun P=>quadraticPolarRead q (P.comp J) t=θ))]
    apply avg_congr
    intro z hz
    have hS : S z:=not_not.mp (fun hn=>hz (unifOn_carried S z hn))
    exact quadratic_row_orbit q hq C J θ ht hS.1 hS.2.symm hroom
  rw [he]
  change avg ν (fun z=>avg w (fun P=>ind (quadraticPolarRead q (P.comp J) z=θ)))≤_
  rw [avg_avg]
  have hc (P : B→ₗ[F]V) (hP : w P≠0) :
      pr ν (fun z=>quadraticPolarRead q (P.comp J) z=θ)≤a⁻¹*bp (-(dim R:ℝ)) := by
    have hframe : quadraticFramesAt q C P:=not_not.mp
      (fun hn=>hP (unifOn_carried _ P hn))
    have hsurj:=quadratic_polar_read_surjective q hq (P.comp J) (hframe.1.comp hJ)
    have hpr : pr unif (fun z=>quadraticPolarRead q (P.comp J) z=θ)=bp (-(dim R:ℝ)) := by
      change mapW unif (quadraticPolarRead q (P.comp J)) θ=_
      rw [map_unif_surjective _ hsurj,unif_apply,card_space,bp_neg]
      rw [dim,Subspace.dual_finrank_eq]
    exact (pr_cap hv _).trans_eq (congrArg (a⁻¹*·) hpr)
  let f (P : B→ₗ[F]V):=if w P=0 then 0 else
    pr ν (fun z=>quadraticPolarRead q (P.comp J) z=θ)
  have hf : avg w (fun P=>pr ν (fun z=>quadraticPolarRead q (P.comp J) z=θ))=avg w f:=
    avg_congr (fun P hP=>by simp only [f,if_neg hP])
  change avg w (fun P=>pr ν (fun z=>quadraticPolarRead q (P.comp J) z=θ))≤_
  rw [hf]
  have hb : 0≤a⁻¹*bp (-(dim R:ℝ)):=mul_nonneg (inv_nonneg.mpr ha.le) (bp_pos _).le
  apply (unifOn_sub _).avg_le hb
  intro P
  dsimp only [f]
  split_ifs with hP
  · exact hb
  exact hc P hP

end
end Lax793645Proofs.Simplifications
