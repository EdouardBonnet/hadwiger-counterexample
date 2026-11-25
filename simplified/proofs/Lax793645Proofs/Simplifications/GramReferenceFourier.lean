import Lax793645Proofs.Simplifications.HighRankBatchWeights

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

theorem gram_linear_phase_bound (M : Mat I I) (ξ : KeyCoordinates I N) :
    |avg unif (fun x=>wsign (gramPrimitive M x)*vectorPhase ξ x)|≤
      bp (-(N:ℝ)*M.rank/2) := by
  let f (X : PlusRack I N):=wsign (∑ u,∑ i,ξ (u,(false,i))*X u i)
  let g (X : PlusRack I N):=wsign (∑ u,∑ i,ξ (u,(true,i))*X u i)
  have hc (x : KeyCoordinates I N) : vectorPhase ξ x=f (keyPlus x)*g (keyMinus x) := by
    unfold vectorPhase dotProduct f g
    rw [←wsign_add]
    congr 1
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib]
    rw [add_comm]
    rfl
  let H (x : Rack I N):=phasedBy M x*(f x.1*g x.2)
  have he : avg unif (fun x=>wsign (gramPrimitive M x)*vectorPhase ξ x)=avg unif H := by
    have hh:=mapW_avg unif (rackCoordinates I N).toEquiv H
    rw [unif_equiv] at hh
    rw [hh]
    apply avg_congr
    intro x _
    rw [hc]
    rfl
  rw [he,pair_unif,pairW_avg,avg_avg]
  have hinner y : avg unif (fun x=>H (x,y))=g y*avg unif (fun x=>f x*wsign (layerPhase M N x y)) := by
    rw [←avg_mul']
    apply avg_congr
    intro x _
    dsimp [H,phasedBy]
    ring
  simp_rw [hinner]
  have hh:=walsh_bound (layerPhase M N) f g (fun _=>(wsign_abs _).le) (fun _=>(wsign_abs _).le)
  rw [layer_rank,Nat.cast_mul] at hh
  simpa only [neg_mul] using hh

theorem unif_vector_phase (ξ : Vec I) : avg unif (vectorPhase ξ)=ind (ξ=0) := by
  have hh:=linear_fourier_character (0 : Vec I) ξ
  change avg unif (fun x=>wsign (dotProduct ξ x))=_
  simpa only [linearFourier,vectorPhase,zero_dotProduct,wsign_zero,mul_one] using hh

theorem gram_indicator_fourier (E : Rail I) (Z : Vec E) (ξ : KeyCoordinates I N) :
    |linearFourier (fun x=>ind (traced (keyPlus x,keyMinus x) E Z)) ξ-
      bp (-num E)*ind (ξ=0)|≤bp (-(N:ℝ)/2) := by
  let A (v : Vec E):=vectorPhase v Z*avg unif
    (fun x : KeyCoordinates I N=>wsign (gramPrimitive (ledgerM E v) x)*vectorPhase ξ x)
  have he : linearFourier (fun x=>ind (traced (keyPlus x,keyMinus x) E Z)) ξ=avg unif A := by
    unfold linearFourier
    simp_rw [rail_expand]
    have hprod x : vectorPhase ξ x*avg unif
        (fun v : Vec E=>phasedBy (ledgerM E v) (keyPlus x,keyMinus x)*vectorPhase v Z)=
        avg unif (fun v : Vec E=>vectorPhase v Z*
          (wsign (gramPrimitive (ledgerM E v) x)*vectorPhase ξ x)) := by
      rw [←avg_mul']
      apply avg_congr
      intro v _
      unfold phasedBy gramPrimitive
      ring
    simp_rw [hprod]
    rw [avg_avg]
    apply avg_congr
    intro v _
    rw [avg_mul']
  have hzero : A 0=ind (ξ=0) := by
    dsimp only [A]
    rw [ledger_zero]
    have hz (x : KeyCoordinates I N) : gramPrimitive (0 : Mat I I) x=0:=by
      rw [gramPrimitive,layer_form]
      simp [mpair]
    simp only [vectorPhase,zero_dotProduct,wsign_zero,one_mul,hz]
    exact unif_vector_phase ξ
  have hv (v : Vec E) : |A v-ind (v=0)*ind (ξ=0)|≤bp (-(N:ℝ)/2) := by
    by_cases hz : v=0
    · rw [hz,hzero,ind_one rfl,one_mul,sub_self,abs_zero]
      exact (bp_pos _).le
    · rw [ind_zero hz,zero_mul,sub_zero]
      dsimp only [A]
      rw [abs_mul,vectorPhase,wsign_abs,one_mul]
      have hM : ledgerM E v≠0:=by
        intro h
        have hh:=inLedger E v
        rw [h] at hh
        apply hz
        exact hh.symm.trans rfl
      have hr:=nonzero_matrix_rank (ledgerM E v) hM
      refine (gram_linear_phase_bound (ledgerM E v) ξ).trans (bp_le ?_)
      have hh : (1:ℝ)≤(ledgerM E v).rank:=by exact_mod_cast hr
      nlinarith only [mul_le_mul_of_nonneg_left hh (show 0≤(N:ℝ) from Nat.cast_nonneg _)]
  have hm : avg (unif : Wgt (Vec E)) (fun v=>ind (v=0))=bp (-num E) := by
    change pr unif (·=0)=_
    rw [pr_point',unif_apply,card_space,dim_vec,bp_neg]
  rw [he]
  have hh:=abs_avg_le (w:=unif) (f:=fun v=>A v-ind (v=0)*ind (ξ=0)) unif_law.nz
  rw [avg_sub,avg_mul,hm] at hh
  exact hh.trans (unif_law.avg_le hv)

end
end Lax793645Proofs.Simplifications
