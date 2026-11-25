import Lax793645Proofs.Simplifications.HyperbolicExtension
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem hyperbolic_gauss (h : ℕ) :
    avg unif (fun v : Hyperbolic h=>wsign (hyperbolicQuadratic h v))=bp (-(h:ℝ)) := by
  classical
  rw [pair_unif,pairW_avg]
  have hi (x : Vec (Fin h)) : avg unif (fun y=>wsign (dotProduct x y))=ind (x=0) := by
    have hh := wsign_lin (dotL x)
    have he : dotL x=0 ↔ x=0 := by
      constructor
      · intro hz
        exact dot_ext_zero (fun y=>by rw [dotProduct_comm]; exact LinearMap.congr_fun hz y)
      · rintro rfl
        apply LinearMap.ext
        intro y
        exact zero_dotProduct y
    rw [he] at hh
    exact hh
  simp only [hyperbolic_apply,hi]
  have hh := pr_unif_lin (LinearMap.id : Vec (Fin h)→ₗ[F] Vec (Fin h)) 0
  rw [ind_one (LinearMap.range (LinearMap.id : Vec (Fin h)→ₗ[F] Vec (Fin h))).zero_mem,one_mul] at hh
  have hr := rk_inj.mp (show Function.Injective
    (LinearMap.id : Vec (Fin h)→ₗ[F] Vec (Fin h)) from fun _ _ h=>h)
  rw [dim_vec,Fintype.card_fin] at hr
  rw [hr] at hh
  change pr unif (fun x : Vec (Fin h)=>x=0)=_
  exact hh

theorem hyperbolic_fourier (h : ℕ) (t : Hyperbolic h) :
    avg unif (fun v : Hyperbolic h=>wsign
      (hyperbolicQuadratic h v+(hyperbolicQuadratic h).polarBilin t v))=
      wsign (hyperbolicQuadratic h t)*bp (-(h:ℝ)) := by
  classical
  let q := hyperbolicQuadratic h
  let E : Hyperbolic h≃Hyperbolic h := ⟨(·+t),(·+t),add_polar t,add_polar t⟩
  have he := avg_bij E unif (fun v=>wsign (q v))
  change avg unif (fun v=>wsign (q (v+t)))=avg unif (fun v=>wsign (q v)) at he
  have hx (v : Hyperbolic h) : q v+q.polarBilin t v=q (v+t)+q t := by
    rw [QuadraticMap.map_add q,←QuadraticMap.polarBilin_apply_apply]
    have hs : q.polarBilin v t=q.polarBilin t v := by
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]
    rw [hs]
    ring_nf
    simp [show (2:F)=0 from by decide]
  change avg unif (fun v=>wsign (q v+q.polarBilin t v))=_
  simp_rw [hx,wsign_add]
  rw [avg_mul,he,hyperbolic_gauss,mul_comm]

/-- Exact quadratic character sum on an affine system of polar equations.
Multiplying by the ambient cardinality gives the proposed frame-count
identity (4); no independence of the prescribed columns is needed here. -/
theorem hyperbolic_affine_sum {I : Type} [Fintype I] [DecidableEq I]
    (h : ℕ) (L : Hyperbolic h→ₗ[F] Vec I) (P : Vec I→ₗ[F] Hyperbolic h)
    (hP : ∀ t v,(hyperbolicQuadratic h).polarBilin (P t) v=dotProduct t (L v))
    (b : Vec I) :
    avg unif (fun v : Hyperbolic h=>ind (L v=b)*wsign (hyperbolicQuadratic h v))=
      bp (-(h:ℝ))*avg unif (fun t : Vec I=>
        wsign (hyperbolicQuadratic h (P t)+dotProduct t b)) := by
  classical
  simp_rw [vector_expand,←avg_mul]
  rw [avg_avg]
  have he (t : Vec I) :
      avg unif (fun v : Hyperbolic h=>
        vectorPhase t (L v)*vectorPhase t b*wsign (hyperbolicQuadratic h v))=
      bp (-(h:ℝ))*wsign (hyperbolicQuadratic h (P t)+dotProduct t b) := by
    have hh (v : Hyperbolic h) :
        vectorPhase t (L v)*vectorPhase t b*wsign (hyperbolicQuadratic h v)=
        wsign (hyperbolicQuadratic h v+(hyperbolicQuadratic h).polarBilin (P t) v)*
          wsign (dotProduct t b) := by
      simp only [vectorPhase,hP,wsign_add]
      ring
    simp_rw [hh]
    rw [avg_mul,hyperbolic_fourier,wsign_add]
    ring
  simp_rw [he]
  exact avg_mul' _ _ _

theorem polar_coordinates_surjective {I : Type} [Fintype I] [DecidableEq I]
    (h : ℕ) (L : Hyperbolic h→ₗ[F] Vec I) (P : Vec I→ₗ[F] Hyperbolic h)
    (hinj : Function.Injective P)
    (hP : ∀ t v,(hyperbolicQuadratic h).polarBilin (P t) v=dotProduct t (L v)) :
    Function.Surjective L := by
  intro b
  obtain ⟨f,hf⟩ := LinearMap.dualMap_surjective_of_injective hinj (dotL b)
  let β : LinearMap.BilinForm F (Hyperbolic h) := (hyperbolicQuadratic h).polarBilin
  let v := (β.toDual (hyperbolic_nondegenerate h)).symm f
  refine ⟨v,?_⟩
  apply sub_eq_zero.mp
  apply dot_ext_zero
  intro t
  rw [dotProduct_sub]
  apply sub_eq_zero.mpr
  have hh := LinearMap.congr_fun hf t
  change f (P t)=dotProduct b t at hh
  have hβ : β v (P t)=f (P t) :=
    LinearMap.BilinForm.apply_toDual_symm_apply (B:=β) (hB:=hyperbolic_nondegenerate h) f (P t)
  have hs : β v (P t)=β (P t) v := by
    simp only [β,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]
  rw [hs,hP] at hβ
  simpa only [dotProduct_comm] using hβ.trans hh

private lemma bit_indicator (x a : F) : ind (x=a)=(1+wsign x*wsign a)/2 := by
  rcases bit_cases x with rfl|rfl <;> rcases bit_cases a with rfl|rfl <;>
    norm_num [ind,wsign]

/-- Exact mass of an affine polar fiber with one prescribed quadratic bit. -/
theorem hyperbolic_affine_bit {I : Type} [Fintype I] [DecidableEq I]
    (h : ℕ) (L : Hyperbolic h→ₗ[F] Vec I) (P : Vec I→ₗ[F] Hyperbolic h)
    (hinj : Function.Injective P)
    (hP : ∀ t v,(hyperbolicQuadratic h).polarBilin (P t) v=dotProduct t (L v))
    (b : Vec I) (a : F) :
    pr unif (fun v : Hyperbolic h=>L v=b ∧ hyperbolicQuadratic h v=a)=
      (bp (-num I)+wsign a*bp (-(h:ℝ))*avg unif (fun t : Vec I=>
        wsign (hyperbolicQuadratic h (P t)+dotProduct t b)))/2 := by
  have hsurj := polar_coordinates_surjective h L P hinj hP
  have hlin : pr unif (fun v=>L v=b)=bp (-num I) := by
    have hh := pr_unif_lin L b
    have hr := rk_surj.mp hsurj
    have hb : b∈L.range := hsurj b
    rw [ind_one hb,one_mul,hr,dim_vec] at hh
    exact hh
  unfold pr
  simp only [ind_and,bit_indicator]
  have he (v : Hyperbolic h) :
      ind (L v=b)*((1+wsign (hyperbolicQuadratic h v)*wsign a)/2)=
      (ind (L v=b)+wsign a*(ind (L v=b)*wsign (hyperbolicQuadratic h v)))/2 := by ring
  simp_rw [he]
  rw [avg_div,avg_add,avg_mul',hyperbolic_affine_sum h L P hP b]
  change (pr unif (fun v=>L v=b)+_)/2=_
  rw [hlin]
  ring

end
end Lax793645Proofs.Simplifications
