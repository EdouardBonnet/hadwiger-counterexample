import Lax793645Proofs.Simplifications.QuadraticRailSpaces
import Lax793645Proofs.Simplifications.GramReferenceBias

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- The number of independent quadratic Gram constraints, including
self-values. Ordered products of the two hyperbolic halves are not fixed. -/
def quadraticReferenceCost (E : Rail I) : ℝ := Module.finrank F (symmetricRail E)

theorem quadratic_indicator_fourier (E : Rail I) (Z : Mat I I)
    (ξ : KeyCoordinates I N) :
    |linearFourier (fun x=>ind (quadraticTraced E Z x)) ξ-
      bp (-quadraticReferenceCost E)*ind (ξ=0)| ≤ bp (-(N:ℝ)/2) := by
  let A (M : symmetricRail E):=wsign (mpair M.val Z)*avg unif
    (fun x : KeyCoordinates I N=>wsign (gramPrimitive M.val x)*vectorPhase ξ x)
  have he : linearFourier (fun x=>ind (quadraticTraced E Z x)) ξ=avg unif A := by
    unfold linearFourier
    simp_rw [quadratic_rail_expansion]
    have hprod x : vectorPhase ξ x*avg unif
        (fun M : symmetricRail E=>wsign (mpair M.val Z)*wsign (gramPrimitive M.val x))=
        avg unif (fun M : symmetricRail E=>wsign (mpair M.val Z)*
          (wsign (gramPrimitive M.val x)*vectorPhase ξ x)) := by
      rw [←avg_mul']
      apply avg_congr
      intro M _
      ring
    simp_rw [hprod]
    rw [avg_avg]
    apply avg_congr
    intro M _
    rw [avg_mul']
  have hzero : A 0=ind (ξ=0) := by
    have hz (x : KeyCoordinates I N) : gramPrimitive (0 : Mat I I) x=0:=by
      rw [gramPrimitive,layer_form]
      simp [mpair]
    dsimp only [A]
    have hm : mpair (0 : Mat I I) Z=0 := by simp [mpair]
    simp only [Submodule.coe_zero,hm,hz,wsign_zero,one_mul]
    exact unif_vector_phase ξ
  have hv (M : symmetricRail E) : |A M-ind (M=0)*ind (ξ=0)| ≤ bp (-(N:ℝ)/2) := by
    by_cases hz : M=0
    · rw [hz,hzero,ind_one rfl,one_mul,sub_self,abs_zero]
      exact (bp_pos _).le
    · rw [ind_zero hz,zero_mul,sub_zero]
      dsimp only [A]
      rw [abs_mul,wsign_abs,one_mul]
      have hM : M.val≠0:=fun h=>hz (Subtype.ext h)
      have hr:=nonzero_matrix_rank M.val hM
      refine (gram_linear_phase_bound M.val ξ).trans (bp_le ?_)
      have hh : (1:ℝ)≤M.val.rank:=by exact_mod_cast hr
      nlinarith only [mul_le_mul_of_nonneg_left hh (show 0≤(N:ℝ) from Nat.cast_nonneg _)]
  have hm : avg (unif : Wgt (symmetricRail E)) (fun M=>ind (M=0))=
      bp (-quadraticReferenceCost E) := by
    change pr unif (·=0)=_
    rw [pr_point',unif_apply,card_space,bp_neg]
    rfl
  rw [he]
  have hh:=abs_avg_le (w:=unif) (f:=fun M=>A M-ind (M=0)*ind (ξ=0)) unif_law.nz
  rw [avg_sub,avg_mul,hm] at hh
  exact hh.trans (unif_law.avg_le hv)

theorem quadratic_reference_mass (E : Rail I) (Z : Mat I I) :
    |pr unif (quadraticTraced E Z : KeyCoordinates I N→Prop)-
      bp (-quadraticReferenceCost E)| ≤ bp (-(N:ℝ)/2) := by
  have hh:=quadratic_indicator_fourier (N:=N) E Z 0
  simpa only [linearFourier,vectorPhase,zero_dotProduct,wsign_zero,one_mul,
    eq_self_iff_true,ind_true,mul_one,pr] using hh

/-- The quadratic reference law has exponentially small nonzero linear
Fourier coefficients, uniformly over the prescribed Gram data. -/
theorem quadratic_reference_bias (E : Rail I) (Z : Mat I I)
    (hN : bp (-(N:ℝ)/2)≤bp (-quadraticReferenceCost E)/2) :
    IsLaw (unifOn (quadraticTraced E Z : KeyCoordinates I N→Prop)) ∧
    bp (-quadraticReferenceCost E)/2≤pr unif (quadraticTraced E Z : KeyCoordinates I N→Prop) ∧
    ∀ ξ : KeyCoordinates I N,ξ≠0 →
      |avg (unifOn (quadraticTraced E Z)) (vectorPhase ξ)|≤
        2*bp (quadraticReferenceCost E)*bp (-(N:ℝ)/2) := by
  let K:=quadraticTraced E Z (N:=N)
  have hmass:=quadratic_reference_mass (N:=N) E Z
  have hlow : bp (-quadraticReferenceCost E)/2≤pr unif K := by
    have hh: bp (-quadraticReferenceCost E)-pr unif K≤bp (-(N:ℝ)/2):=
      (le_abs_self _).trans (by rwa [abs_sub_comm])
    linarith only [hh,hN]
  have hpos : 0<pr unif K := (half_pos (bp_pos _)).trans_le hlow
  obtain ⟨x,hx,_⟩:=exists_of_pr_pos unif_law.nz hpos
  refine ⟨unifOn_law ⟨x,hx⟩,hlow,fun ξ hξ=>?_⟩
  have hh:=quadratic_indicator_fourier (N:=N) E Z ξ
  rw [ind_zero hξ,mul_zero,sub_zero] at hh
  have he : linearFourier (fun x=>ind (K x)) ξ=
      pr unif K*avg (unifOn K) (vectorPhase ξ) := by
    rw [←part_reset K _ hpos]
    unfold linearFourier partMean
    apply avg_congr
    intro x _
    ring
  change |linearFourier (fun x=>ind (K x)) ξ|≤_ at hh
  rw [he,abs_mul,abs_of_pos hpos] at hh
  have hscale : (bp (-quadraticReferenceCost E)/2)*(2*bp (quadraticReferenceCost E))=1 := by
    rw [bp_neg]
    field_simp [(bp_pos (quadraticReferenceCost E)).ne']
  apply le_of_mul_le_mul_left _ (half_pos (bp_pos (-quadraticReferenceCost E)))
  calc
    _≤pr unif K*|avg (unifOn K) (vectorPhase ξ)|:=
      mul_le_mul_of_nonneg_right hlow (abs_nonneg _)
    _≤bp (-(N:ℝ)/2):=hh
    _=(bp (-quadraticReferenceCost E)/2)*(2*bp (quadraticReferenceCost E)*bp (-(N:ℝ)/2)):=by
      rw [←mul_assoc,hscale,one_mul]

end
end Lax793645Proofs.Simplifications
