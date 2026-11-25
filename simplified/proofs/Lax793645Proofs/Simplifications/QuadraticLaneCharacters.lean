import Lax793645Proofs.Simplifications.QuadraticReferenceFourier
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.IndependentWeightCorrelation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : ℕ}

/-- Cross-batch quadratic Gram constraints decorrelate arbitrary bounded
tests on the individual batches. Only symmetric coefficients are expanded. -/
theorem quadratic_cross_expand (f : I→Wgt (Rack J N))
    (hf : ∀ i x,|f i x|≤1) (E : Rail (I×J)) (Z : Mat (I×J) (I×J))
    (hE : ∀ x∈E,x.1.1≠x.2.1) :
    |avg unif (fun x : Rack (I×J) N=>
      ind (quadraticTraced E Z ((rackCoordinates (I×J) N).symm x))*brightProd f x)-
      bp (-quadraticReferenceCost E)*avg unif (brightProd f)|≤bp (-(N:ℝ)/2) := by
  let A (M : symmetricRail E):=wsign (mpair M.val Z)*avg unif
    (fun x : Rack (I×J) N=>phasedBy M.val x*brightProd f x)
  have he : avg unif (fun x : Rack (I×J) N=>
      ind (quadraticTraced E Z ((rackCoordinates (I×J) N).symm x))*brightProd f x)=
      avg unif A := by
    simp_rw [quadratic_rail_expansion,←avg_mul]
    rw [avg_avg]
    apply avg_congr
    intro M _
    dsimp only [A]
    rw [←avg_mul']
    apply avg_congr
    intro x _
    change (_*phasedBy M.val x)*brightProd f x=_
    ring
  have hz : A 0=avg unif (brightProd f) := by
    simp only [A,Submodule.coe_zero,mpair_comm (0 : Mat (I×J) (I×J)),
      map_zero,wsign_zero,layer_zero,one_mul]
  have hb (M : symmetricRail E) :
      |A M-ind (M=0)*avg unif (brightProd f)|≤bp (-(N:ℝ)/2) := by
    by_cases hM : M=0
    · rw [hM,hz,ind_one rfl,one_mul,sub_self,abs_zero]
      exact (bp_pos _).le
    rw [ind_zero hM,zero_mul,sub_zero]
    dsimp only [A]
    rw [abs_mul,wsign_abs,one_mul]
    obtain ⟨x,y,hxy⟩ : ∃ x y,M.val x y=1 := by
      by_contra! h
      apply hM
      apply Subtype.ext
      ext x y
      exact (bit_cases _).resolve_right (h x y)
    have hm : (x,y)∈E := by
      by_contra h
      have hh:=M.property.2 x y h
      rw [hxy] at hh
      exact one_ne_zero hh
    exact speed M.val (hE _ hm) hxy f hf
  have hmass : avg (unif : Wgt (symmetricRail E)) (fun M=>ind (M=0))=
      bp (-quadraticReferenceCost E) := by
    change pr unif (·=0)=_
    rw [pr_point',unif_apply,card_space,bp_neg]
    rfl
  rw [he]
  have hh:=abs_avg_le (w:=unif)
    (f:=fun M : symmetricRail E=>A M-ind (M=0)*avg unif (brightProd f)) unif_law.nz
  rw [avg_sub,avg_mul,hmass] at hh
  exact hh.trans (unif_law.avg_le hb)

end
end Lax793645Proofs.Simplifications
