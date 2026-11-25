import Lax793645Proofs.Simplifications.QuadraticStatusFourier
import Lax793645Proofs.Simplifications.QueryCappedMoment
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ZeroDiscrepancyPrediction

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

/-- The linear part of one selected point, expressed in the original
independent query coordinates. -/
def inputRayLinear (v : Template p I) (i : I) :
    Vec (I×Block p.g×Fin n)→ₗ[F] Ray p n where
  toFun x:=putLab p n (v.s i) (Option.elim' 0 (lit (v.f i) (v.t i)
    (inputCoordinates p n I x i)))
  map_add' x y:=by
    rw [←map_add]
    congr 1
    funext j
    cases j with
    | none => simp
    | some j =>
        by_cases h : (v.f i).keeps (v.t i) j.1 <;>
          simp [lit,h,inputCoordinates]
  map_smul' a x:=by
    rw [←map_smul]
    congr 1
    funext j
    cases j with
    | none => simp
    | some j =>
        by_cases h : (v.f i).keeps (v.t i) j.1 <;>
          simp [lit,h,inputCoordinates]

omit [Fintype I] [DecidableEq I] in
theorem input_ray_affine (v : Template p I) (i : I)
    (x : Vec (I×Block p.g×Fin n)) :
    point p (v.s i) (lit (v.f i) (v.t i) (inputCoordinates p n I x i))=
      inputRayLinear v i x+point p (v.s i) (0 : Base p.g n) := by
  change putLab p n (v.s i) _=putLab p n (v.s i) _+putLab p n (v.s i) _
  rw [←map_add]
  congr 1
  funext j
  cases j <;> simp [baseV]

/-- The p-bit has bounded Fourier complexity at every orientation. No
cap, independence, or genericity hypothesis on that orientation is used. -/
theorem inner_status_fourier (v : Template p I) (o : UnitType p n N) (i : I)
    (φ : Wgt F) (hφ : ∀ a,|φ a|≤1) :
    inputFourierNorm (fun x=>φ (innerP p o (v.aim i)
      (useAtom p (v.t i) (v.s i) (v.f i) (x i))))≤
        bp ((tagDegree p.g*p.h:ℕ):ℝ) := by
  obtain ⟨M,hM,he⟩:=inner_gem p o (v.aim i) (v.t i)
  have hp x : innerP p o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i)
      (inputCoordinates p n I x i))=
      evmat M (inputRayLinear v i x+point p (v.s i) (0 : Base p.g n))
        (inputRayLinear v i x+point p (v.s i) (0 : Base p.g n)) := by
    rw [useAtom,he,mom,mpair_outer,input_ray_affine]
  unfold inputFourierNorm
  simp_rw [hp]
  exact (affine_quadratic_status_fourier M (inputRayLinear v i)
    (point p (v.s i) (0 : Base p.g n)) φ hφ).trans (bp_le (by exact_mod_cast hM))

def queryPWeights (v : Template p I) (a : I→F) (o : UnitType p n N) : Wgt (Inputs p n I) :=
  fun x=>∏ i,ind (innerP p o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i) (x i))=a i)

theorem query_p_weights_norm (v : Template p I) (a : I→F) (o : UnitType p n N) :
    inputFourierNorm (queryPWeights v a o)≤bp (num I*(tagDegree p.g*p.h:ℕ)) := by
  unfold inputFourierNorm queryPWeights
  refine (fourier_norm_product _).trans ?_
  have hh i:=inner_status_fourier v o i (fun z=>ind (z=a i))
    (fun z=>by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _)
  refine (Finset.prod_le_prod (fun i _=>fourier_norm_nonneg _)
    (fun i _=>hh i)).trans_eq ?_
  rw [Finset.prod_const,Finset.card_univ]
  rw [←bp_mul_nat]
  congr 1
  unfold num
  ring

theorem query_p_weights_indicator (v : Template p I) (a : I→F)
    (o : UnitType p n N) (x : Inputs p n I) :
    queryPWeights v a o x=ind (∀ i,innerP p o (v.aim i)
      (useAtom p (v.t i) (v.s i) (v.f i) (x i))=a i) := by
  unfold queryPWeights
  by_cases h : ∀ i,innerP p o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i) (x i))=a i
  · rw [ind_one h]
    simp only [h,ind_true,Finset.prod_const_one]
  · rw [ind_zero h]
    push Not at h
    obtain ⟨i,hi⟩:=h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ind_zero hi)

end
end Lax793645Proofs.Simplifications
