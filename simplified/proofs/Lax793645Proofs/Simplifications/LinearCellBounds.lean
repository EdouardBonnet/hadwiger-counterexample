import Lax793645Proofs.Simplifications.QuadraticStatusFourier
import Lax793645Proofs.Simplifications.GramReferenceFourier
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UnfilteredHistogramEnergy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem fourier_norm_linear_fiber (P : Mat J I) (a : Vec J) :
    fourierNorm (fun x=>ind (P*ᵥx=a))≤1 := by
  have he x : ind (P*ᵥx=a)=avg unif (fun ξ : Vec J=>
      vectorPhase ξ a*vectorPhase (Pᵀ*ᵥξ) x) := by
    rw [vector_expand]
    apply avg_congr
    intro ξ _
    unfold vectorPhase
    rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose,mul_comm]
  simp_rw [he]
  refine (fourier_norm_avg unif unif_law.nz
    (fun ξ : Vec J=>fun x : Vec I=>vectorPhase ξ a*vectorPhase (Pᵀ*ᵥξ) x)).trans_eq ?_
  have hchar ξ : fourierNorm (fun x : Vec I=>vectorPhase (Pᵀ*ᵥξ) x)=1:=
    fourier_norm_character (Pᵀ*ᵥξ)
  simp_rw [fourier_norm_smul,hchar]
  simp only [mul_one,vectorPhase,wsign_abs]
  exact (unif_law (α:=Vec J)).avg_const 1

theorem small_bias_test (ν : Wgt (Vec I)) (hν : IsLaw ν) (γ : ℝ) (hγ : 0≤γ)
    (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ) (f : Wgt (Vec I)) :
    |avg ν f-avg unif f|≤γ*fourierNorm f := by
  have he (μ : Wgt (Vec I)) : avg μ f=∑ ξ,linearFourier f ξ*avg μ (vectorPhase ξ) := by
    have hx x : f x=∑ ξ,linearFourier f ξ*vectorPhase ξ x:=(hat_eqn f x).symm
    change avg μ (fun x=>f x)=_
    simp_rw [hx,avg_sum,avg_mul']
  have hz : avg ν (vectorPhase (0 : Vec I))=1 := by
    change avg ν (fun x=>vectorPhase (0 : Vec I) x)=1
    simp only [vectorPhase,zero_dotProduct,wsign_zero,hν.avg_const]
  have hb ξ : |avg ν (vectorPhase ξ)-avg unif (vectorPhase ξ)|≤γ := by
    rw [unif_vector_phase]
    by_cases hξ : ξ=0
    · rw [hξ,hz,ind_one rfl,sub_self,abs_zero]
      exact hγ
    · rw [ind_zero hξ,sub_zero]
      exact hbias ξ hξ
  rw [he ν,he unif,←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul]
  exact (Finset.sum_le_sum (fun ξ _=>mul_le_mul_of_nonneg_left (hb ξ) (abs_nonneg _))).trans_eq
    (by rw [←Finset.sum_mul,mul_comm]; rfl)

theorem linear_cell_mass_error (ν : Wgt (Vec I)) (hν : IsLaw ν) (γ : ℝ) (hγ : 0≤γ)
    (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (a : Vec J) :
    |mapW ν P.mulVec a-mapW unif P.mulVec a|≤γ := by
  exact (small_bias_test ν hν γ hγ hbias (fun x=>ind (P*ᵥx=a))).trans
    ((mul_le_mul_of_nonneg_left (fourier_norm_linear_fiber P a) hγ).trans_eq (mul_one _))

/-- Every nonempty linear cell has reference mass bounded below in terms
of the number of equations, once the Gram law's linear bias is small. -/
theorem linear_cells_stamina (ν : Wgt (Vec I)) (hν : IsLaw ν) (γ : ℝ) (hγ : 0≤γ)
    (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (hsmall : γ≤bp (-num J)/2) :
    stamina (mapW ν P.mulVec) (bp (-num J)/2) := by
  intro a ha
  have hpos : 0<mapW ν P.mulVec a:=lt_of_le_of_ne (map_nz hν.nz _ _) (Ne.symm ha)
  obtain ⟨x,hx,_⟩:=exists_of_pr_pos hν.nz hpos
  have hr : a∈LinearMap.range P.mulVecLin:=⟨x,hx⟩
  have hm : mapW (unif : Wgt (Vec I)) P.mulVec a=bp (-(P.rank:ℝ)) := by
    have hh:=pr_unif_lin P.mulVecLin a
    rw [ind_one hr,one_mul] at hh
    exact hh
  have hlow : bp (-num J)≤mapW (unif : Wgt (Vec I)) P.mulVec a:=by
    rw [hm]
    apply bp_le
    have hh:=Matrix.rank_le_card_height P
    exact neg_le_neg (by exact_mod_cast hh)
  have he:=linear_cell_mass_error ν hν γ hγ hbias P a
  have hh: mapW unif P.mulVec a-mapW ν P.mulVec a≤γ:=
    (le_abs_self _).trans (by rwa [abs_sub_comm])
  linarith only [hlow,hh,hsmall]

theorem linear_cell_reference_comparison (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (γ : ℝ) (hγ : 0≤γ)
    (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (hsmall : γ≤bp (-num J)/2) (a : Vec J) :
    mapW unif P.mulVec a≤2*mapW ν P.mulVec a := by
  by_cases ha : a∈P.mulVecLin.range
  · have hm : mapW unif P.mulVec a=bp (-(P.rank:ℝ)):=by
      change pr unif (fun x=>P.mulVecLin x=a)=_
      rw [pr_unif_lin,ind_one ha,one_mul]
      rfl
    have hlo : bp (-num J)≤mapW unif P.mulVec a:=by
      rw [hm]
      apply bp_le
      have h:=P.rank_le_card_height
      exact neg_le_neg (by exact_mod_cast h)
    have herr:=linear_cell_mass_error ν hν γ hγ hbias P a
    have hgap : mapW unif P.mulVec a-mapW ν P.mulVec a≤γ:=by
      exact (le_abs_self _).trans (by simpa only [abs_sub_comm] using herr)
    linarith only [hlo,hsmall,hgap]
  · have hz : mapW unif P.mulVec a=0:=by
      change pr unif (fun x=>P.mulVecLin x=a)=_
      rw [pr_unif_lin,ind_zero ha,zero_mul]
    rw [hz]
    exact mul_nonneg (by norm_num) (map_nz hν.nz _ _)

end
end Lax793645Proofs.Simplifications
