import Lax793645Proofs.Simplifications.RetainedFourCornerBatches
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BatchCharacters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J A : Type} [Fintype I] [Fintype J] [Fintype A]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] {N : ℕ}

/-- Ambient coordinate order used by the Fourier lemmas. -/
def rackCoordinates (I : Type) (N : ℕ) : KeyCoordinates I N≃ₗ[F] Rack I N where
  toFun x := (keyPlus x,keyMinus x)
  invFun x v := if v.2.1 then x.2 v.1 v.2.2 else x.1 v.1 v.2.2
  left_inv x := by funext v; rcases v with ⟨u,b,i⟩; cases b <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] [Fintype J] [DecidableEq A] in
theorem batch_off_right (x : Rack (I×J) N) {T : A→I×J} {i : I}
    (B : PlusRack A N) (h : i∉heard T) :
    led i (x+(0,upliftR T B))=led i x := by
  apply Prod.ext
  · ext; simp [led,sectionR]
  ext
  simp only [led,sectionR,Prod.snd_add,Matrix.add_apply,Matrix.submatrix_apply,
    heard_fresh B h,add_zero]

omit [Fintype I] [Fintype J] [DecidableEq A] in
theorem batch_off_left (x : Rack (I×J) N) {T : A→I×J} {i : I}
    (B : PlusRack A N) (h : i∉heard T) :
    led i (x+(upliftR T B,0))=led i x := by
  apply Prod.ext
  · ext
    simp only [led,sectionR,Prod.fst_add,Matrix.add_apply,Matrix.submatrix_apply,
      heard_fresh B h,add_zero]
  ext; simp [led,sectionR]

/-- The disjoint-block rank bound applies to signed bounded batch functions,
not just event indicators. -/
theorem high_rank_batch_product (M : Avenue I J) (f : I→Wgt (Rack J N))
    (hf : ∀ i x,|f i x|≤1) :
    |avg unif (fun x=>phasedBy M x*∏ i,f i (led i x))|≤
      bp (-(N:ℝ)*(peak M:ℝ)/2) := by
  classical
  obtain ⟨T,U,hTU,hA⟩ := real_peak M
  let L := heard T
  let S := univ\L
  let F (V : Finset I) (x : Rack (I×J) N) := ∏ i∈V,f i (led i x)
  have hbound V x : |F V x|≤1 := by
    change |∏ i∈V,f i (led i x)|≤1
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>hf i _)).trans_eq (by simp)
  have he x : (∏ i,f i (led i x))=F L x*F S x := by
    rw [←Finset.prod_union (show Disjoint L S from disjoint_sdiff),
      Finset.union_sdiff_of_subset (Finset.subset_univ L)]
  have hd : Disjoint (heard T) (heard U) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hTU i j he.symm
  have hh := layerLeak M (F L) (F S) (fun _=>1) T U (hbound L) (hbound S)
    (fun x y=>Finset.prod_congr rfl (fun i hi=>by
      rw [batch_off_right x y (fun h=>Finset.disjoint_left.mp hd hi h)]))
    (fun x y=>Finset.prod_congr rfl (fun i hi=>by
      rw [batch_off_left x y (Finset.mem_sdiff.mp hi).2]))
    (fun _ _ _=>rfl)
  have hr : (M.submatrix T U).rank=peak M := (mrk_inj.mp hA).trans (Fintype.card_fin _)
  simp only [mul_one,abs_one,unif_law.avg_const,hr] at hh
  simpa only [he,mul_assoc] using hh

omit [DecidableEq J] in
/-- A full-key character factors over the original batches. -/
theorem rack_character_batches (ξ : KeyCoordinates (I×J) N) (x : Rack (I×J) N) :
    vectorPhase ξ ((rackCoordinates (I×J) N).symm x)=
      ∏ i:I,vectorPhase (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2))))
        ((rackCoordinates J N).symm (led i x)) := by
  unfold vectorPhase dotProduct
  rw [←wsign_sum]
  simp only [Fintype.sum_prod_type]
  congr 1
  have he (u : Fin N) :
      (∑ b:Bool,∑ i:I,∑ j:J,ξ (u,(b,(i,j)))*
        ((rackCoordinates (I×J) N).symm x) (u,(b,(i,j))))=
      ∑ i:I,∑ b:Bool,∑ j:J,ξ (u,(b,(i,j)))*
        ((rackCoordinates (I×J) N).symm x) (u,(b,(i,j))) := Finset.sum_comm
  simp_rw [he]
  rw [Finset.sum_comm]
  rfl

/-- High cross-batch rank still gives cancellation with any joint weight of
bounded Fourier norm. Linear relations and kernel polynomials are permitted. -/
theorem high_rank_batch_weight (M : Avenue I J) (f : I→Wgt (Rack J N))
    (hf : ∀ i x,|f i x|≤1) (w : Wgt (KeyCoordinates (I×J) N)) :
    |avg unif (fun x=>phasedBy M x*(∏ i,f i (led i x))*
      w ((rackCoordinates (I×J) N).symm x))|≤
      bp (-(N:ℝ)*(peak M:ℝ)/2)*fourierNorm w := by
  apply fourier_pullback_bound unif _ (rackCoordinates (I×J) N).symm w _
  intro ξ
  simp_rw [rack_character_batches]
  have hh := high_rank_batch_product M (fun i z=>f i z*
      vectorPhase (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2))))
        ((rackCoordinates J N).symm z)) (fun i z=>by
          simpa only [abs_mul,vectorPhase,wsign_abs,mul_one] using hf i z)
  simpa only [Finset.prod_mul_distrib,mul_assoc] using hh

/-- Fourier coefficient of a product of independent rack functions. -/
theorem rack_product_fourier (f : I→Wgt (Rack J N)) (ξ : KeyCoordinates (I×J) N) :
    avg unif (fun x=>(∏ i,f i (led i x))*vectorPhase ξ ((rackCoordinates (I×J) N).symm x))=
      ∏ i:I,linearFourier (fun z=>f i (rackCoordinates J N z))
        (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2)))) := by
  simp_rw [rack_character_batches,←Finset.prod_mul_distrib]
  rw [led_uniform (fun x : I→Rack J N=>∏ i,f i (x i)*
    vectorPhase (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2))))
      ((rackCoordinates J N).symm (x i)))]
  change avg (prodW (fun _ : I=>unif)) (prodW (fun i z=>f i z*
    vectorPhase (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2))))
      ((rackCoordinates J N).symm z))) = _
  rw [prodW_avg]
  apply Finset.prod_congr rfl
  intro i _
  have hh := mapW_avg unif (rackCoordinates J N).toEquiv
    (fun z=>f i z*vectorPhase (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2))))
      ((rackCoordinates J N).symm z))
  rw [unif_equiv] at hh
  rw [hh]
  unfold linearFourier
  apply avg_congr
  intro z _
  simp only [LinearEquiv.coe_toEquiv,LinearEquiv.symm_apply_apply]
  ring

/-- Independent batch Fourier bounds survive an arbitrary joint weight. -/
theorem rack_product_weight (f : I→Wgt (Rack J N)) (ε : ℝ)
    (hf : ∀ i ξ,|linearFourier (fun z=>f i (rackCoordinates J N z)) ξ|≤ε)
    (w : Wgt (KeyCoordinates (I×J) N)) :
    |avg unif (fun x=>(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x))|≤
      ε^Fintype.card I*fourierNorm w := by
  apply fourier_pullback_bound unif _ (rackCoordinates (I×J) N).symm w _
  intro ξ
  rw [rack_product_fourier,Finset.abs_prod]
  calc
    _≤∏ _ : I,ε := Finset.prod_le_prod (fun i _=>abs_nonneg _)
      (fun i _=>hf i (fun v : Fin N×(Bool×J)=>ξ (v.1,(v.2.1,(i,v.2.2)))))
    _=ε^Fintype.card I := by simp

end
end Lax793645Proofs.Simplifications
