import Lax793645Proofs.Simplifications.QuadraticPolarRows
import Lax793645Proofs.Simplifications.QuadraticImageCaps

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B R D V : Type} [AddCommGroup B] [Module F B]
  [AddCommGroup R] [Module F R] [FiniteDimensional F R]
  [AddCommGroup D] [Module F D] [FiniteDimensional F D]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Fintype (B→ₗ[F]V)] [Fintype (D→ₗ[F]V)]
  [Fintype (D→ₗ[F]Module.Dual F R)]

omit [FiniteDimensional F R] [Fintype (D→ₗ[F]V)]
    [Fintype (D→ₗ[F]Module.Dual F R)] in
theorem quadratic_rows_orbit (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    (C : QuadraticForm F B→Prop) (J : R→ₗ[F]B) (Θ : D→ₗ[F]Module.Dual F R)
    (T Z : D→ₗ[F]V) (hT : Injective T) (hZ : Injective Z)
    (hval : q.comp T=q.comp Z) (hroom : 2*dim D+6≤dim V) :
    pr (unifOn (quadraticFramesAt q C))
        (fun P=>(quadraticPolarRead q (P.comp J)).comp T=Θ)=
      pr (unifOn (quadraticFramesAt q C))
        (fun P=>(quadraticPolarRead q (P.comp J)).comp Z=Θ) := by
  obtain ⟨e,he⟩:=quadratic_frame_symmetry q hq T Z hT hZ
    (fun d=>congrArg (fun Q : QuadraticForm F D=>Q d) hval)
  let E:=quadraticPost (B:=B) q e
  let w:=unifOn (quadraticFramesAt q C)
  have hw (P : B→ₗ[F]V) : w (E P)=w P := by
    simp only [w,E,unifOn_val,←quadratic_post_invar q e C]
  have hp (P : B→ₗ[F]V) : (quadraticPolarRead q ((E P).comp J)).comp Z=
      (quadraticPolarRead q (P.comp J)).comp T := by
    ext d r
    change q.polarBilin (Z d) (e (P (J r)))=q.polarBilin (T d) (P (J r))
    rw [←he d,quadratic_isometry_polar]
  have hh:=avg_bij E w
    (fun P=>ind ((quadraticPolarRead q (P.comp J)).comp Z=Θ))
  simpa only [hw,hp,pr] using hh

/-- Average the prescribed rows over their quadratic orbit, then count
the fibers of a surjective linear map. -/
theorem quadratic_frame_rows_cap (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    (C : QuadraticForm F B→Prop) (J : R→ₗ[F]B) (hJ : Injective J)
    (Θ : D→ₗ[F]Module.Dual F R) (T : D→ₗ[F]V) (hT : Injective T)
    (hroom : 2*dim D+6≤dim V) {a : ℝ} (ha : 0<a)
    (hs : a≤pr unif (quadraticGramGood q (q.comp T))) :
    pr (unifOn (quadraticFramesAt q C))
        (fun P=>(quadraticPolarRead q (P.comp J)).comp T=Θ)≤
      a⁻¹*bp (-(dim D:ℝ)*dim R) := by
  classical
  let S:=quadraticGramGood q (q.comp T)
  let w:=unifOn (quadraticFramesAt q C)
  let ν:=unifOn S
  have hν : IsLaw ν:=unifOn_law ⟨T,hT,rfl⟩
  have hv (Z : D→ₗ[F]V) : ν Z≤a⁻¹*unif Z:=by
    simpa only [on_unif] using on_mon unif_law.nz ha hs Z
  have he : pr w (fun P=>(quadraticPolarRead q (P.comp J)).comp T=Θ)=
      avg ν (fun Z=>pr w (fun P=>(quadraticPolarRead q (P.comp J)).comp Z=Θ)) := by
    rw [←hν.avg_const (pr w (fun P=>(quadraticPolarRead q (P.comp J)).comp T=Θ))]
    apply avg_congr
    intro Z hZ
    have hS : S Z:=not_not.mp (fun hn=>hZ (unifOn_carried S Z hn))
    exact quadratic_rows_orbit q hq C J Θ T Z hT hS.1 hS.2.symm hroom
  rw [he]
  change avg ν (fun Z=>avg w
    (fun P=>ind ((quadraticPolarRead q (P.comp J)).comp Z=Θ)))≤_
  rw [avg_avg]
  have hc (P : B→ₗ[F]V) (hP : w P≠0) :
      pr ν (fun Z=>(quadraticPolarRead q (P.comp J)).comp Z=Θ)≤
        a⁻¹*bp (-(dim D:ℝ)*dim R) := by
    have hframe : quadraticFramesAt q C P:=not_not.mp
      (fun hn=>hP (unifOn_carried _ P hn))
    let A:=quadraticPolarRead q (P.comp J)
    let L : (D→ₗ[F]V)→ₗ[F](D→ₗ[F]Module.Dual F R):={
      toFun:=fun Z=>A.comp Z
      map_add':=by intro X Y; ext d r; simp
      map_smul':=by intro c X; ext d r; simp }
    have hsurj:=quadratic_polar_read_surjective q hq (P.comp J) (hframe.1.comp hJ)
    obtain ⟨s,hs⟩:=A.exists_rightInverse_of_surjective (range_eq_top.mpr hsurj)
    have hcomp : Surjective L := by
      intro Y
      refine ⟨s.comp Y,?_⟩
      change A.comp (s.comp Y)=Y
      rw [←LinearMap.comp_assoc,hs,LinearMap.id_comp]
    have hpr : pr unif (fun Z : D→ₗ[F]V=>A.comp Z=Θ)=bp (-(dim D:ℝ)*dim R) := by
      have hm : mapW unif L=unif:=map_unif_surjective
        (V:=D→ₗ[F]V) (W:=D→ₗ[F]Module.Dual F R) L hcomp
      change mapW unif L Θ=_
      rw [hm,unif_apply,card_space,←bp_neg]
      congr 1
      simp only [dim,Module.finrank_linearMap,Module.finrank_self,Nat.cast_mul,
        mul_one]
      ring
    exact (pr_cap hv _).trans_eq (congrArg (a⁻¹*·) hpr)
  let f (P : B→ₗ[F]V):=if w P=0 then 0 else
    pr ν (fun Z=>(quadraticPolarRead q (P.comp J)).comp Z=Θ)
  have hf : avg w (fun P=>pr ν
      (fun Z=>(quadraticPolarRead q (P.comp J)).comp Z=Θ))=avg w f:=
    avg_congr (fun P hP=>by simp only [f,if_neg hP])
  change avg w (fun P=>pr ν
    (fun Z=>(quadraticPolarRead q (P.comp J)).comp Z=Θ))≤_
  rw [hf]
  have hb : 0≤a⁻¹*bp (-(dim D:ℝ)*dim R):=
    mul_nonneg (inv_nonneg.mpr ha.le) (bp_pos _).le
  apply (unifOn_sub _).avg_le hb
  intro P
  dsimp only [f]
  split_ifs with hP
  · exact hb
  exact hc P hP

section Hyperbolic
variable {I : Type} [Fintype I] [DecidableEq I]

/-- For fixed row count the constant is independent of the observed
dimension and of the quadratic data of the full frame. -/
theorem hyperbolic_frame_rows_cap (N : ℕ)
    [Fintype (B→ₗ[F]Vec (HyperbolicIdx N))]
    [Fintype (Vec I→ₗ[F]Vec (HyperbolicIdx N))]
    [Fintype (Vec I→ₗ[F]Module.Dual F R)]
    (C : QuadraticForm F B→Prop) (J : R→ₗ[F]B) (hJ : Injective J)
    (Θ : Vec I→ₗ[F]Module.Dual F R) (T : Vec I→ₗ[F]Vec (HyperbolicIdx N))
    (hT : Injective T) (hN : 2*num I+3≤N) :
    pr (unifOn (quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm' C))
        (fun P=>(quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' (P.comp J)).comp T=Θ)≤
      bp ((num I)^2+2-num I*dim R) := by
  have hn : 2*Fintype.card I+3≤N:=by exact_mod_cast hN
  have hroom : 2*dim (Vec I)+6≤dim (Vec (HyperbolicIdx N)):=by
    simp only [dim_vec,Fintype.card_sum,Fintype.card_fin]
    omega
  have hl : bp (-(num I)^2-2)≤pr unif
      (quadraticGramGood (hyperbolicMatrix N).toQuadraticForm'
        ((hyperbolicMatrix N).toQuadraticForm'.comp T)) := by
    rw [matrix_quadratic_comp]
    exact quadratic_gram_lower N _ (by linarith)
  refine (quadratic_frame_rows_cap _ (hyperbolic_matrix_nondegenerate N)
    C J hJ Θ T hT hroom (bp_pos _) hl).trans_eq ?_
  rw [←bp_neg,←bp_add]
  congr 1
  simp only [dim_vec,num]
  ring

end Hyperbolic
end
end Lax793645Proofs.Simplifications
