import Lax793645Proofs.Simplifications.QuadraticPatternSum
import Lax793645Proofs.Simplifications.QuadraticNetworkNormalization
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RepeatedQueryBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {N : ℕ}

/-- Repeated hits under the quadratic Gram reference. All symmetric
coefficient patterns are counted; no ordered Gram constraints are added. -/
theorem quadratic_repeated_flood (E : Rail (I×J)) (Z : Mat (I×J) (I×J))
    (u : ℝ) (hu : 0≤u) (P : I→Rack J N→Prop)
    (hp : ∀ i,bp (-u)≤pr unif (P i))
    (hd : peakExpense I J 1+(-(N:ℝ)/2+2*u)≤0) :
    pr unif (fun x : Rack (I×J) N=>
      quadraticTraced E Z ((rackCoordinates (I×J) N).symm x) ∧ ∀ i,P i (led i x)) ≤
      bp (-(dim (symmetricRail E):ℝ))*
        ((num (I×J)+1)*bp (num I*num J*num J))*(∏ i,pr unif (P i)) := by
  let H:=∏ i,pr unif (P i)
  have hH : 0≤H:=Finset.prod_nonneg (fun _ _=>pr_nonneg unif_law.nz)
  let F (M : Avenue I J):=if M∈symmetricRail E then
    wsign (mpair M Z)*avg unif (fun x=>phasedBy M x*phot P x) else 0
  have hlarge M (_ : 0≤peak M) : |F M|≤bp (-((N:ℝ)/2-2*u)*peak M)*H := by
    by_cases hm : M∈symmetricRail E
    · dsimp only [F]
      rw [if_pos hm,abs_mul,wsign_abs,one_mul]
      dsimp only [H]
      convert light_bound M P u hu hp using 1 <;> ring
    · rw [show F M=0 from if_neg hm,abs_zero]
      exact mul_nonneg (bp_pos _).le hH
  have hh:=weighted_pattern_sum_bound F 0 0 ((N:ℝ)/2-2*u) H
    le_rfl hH (by linarith only [hd]) (fun _ h=>by omega) hlarge
  simp only [Nat.cast_zero,mul_zero,zero_add,bp_zero,mul_one] at hh
  have he : pr unif (fun x : Rack (I×J) N=>
      quadraticTraced E Z ((rackCoordinates (I×J) N).symm x) ∧ ∀ i,P i (led i x))=
      bp (-(dim (symmetricRail E):ℝ))*∑ M : Avenue I J,F M := by
    unfold pr
    simp_rw [ind_and,quadratic_rail_expansion,←avg_mul]
    rw [avg_avg]
    have hv (M : symmetricRail E) : avg unif (fun x : Rack (I×J) N=>
        (wsign (mpair M.val Z)*wsign (gramPrimitive M.val ((rackCoordinates (I×J) N).symm x)))*
          ind (∀ i,P i (led i x)))=
        wsign (mpair M.val Z)*avg unif (fun x=>phasedBy M.val x*phot P x) := by
      rw [←avg_mul']
      apply avg_congr
      intro x _
      rw [ind_all]
      change _*phasedBy M.val x*phot P x=_
      ring
    simp_rw [hv]
    have hu (v : Wgt (symmetricRail E)) : avg unif v=
        bp (-(dim (symmetricRail E):ℝ))*∑ M,v M := by
      unfold avg
      simp only [unif_apply,card_space,←bp_neg,←Finset.mul_sum]
    rw [hu]
    congr 1
    exact sum_symmetric_rail E (fun M=>wsign (mpair M Z)*avg unif
      (fun x=>phasedBy M x*phot P x))
  rw [he,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hh) (bp_pos _).le

/-- Independent physical columns, with only their quadratic Gram table
prescribed. Their two coordinate halves may be dependent. -/
def quadraticIndependentNetwork (g : Route (I×J) G) (Q : GeoM g)
    (x : Rack (I×J) N) : Prop:=∀ i,quadraticPairGood (Q i) (rackEquiv g N x i)

theorem quadratic_independent_exact (g : Route (I×J) G) (Q : GeoM g) :
    quadraticIndependentNetwork (N:=N) g Q=
      quadraticExactNetwork g (fun i=>(1 : Mat (Port g i) (Port g i))) Q := by
  funext x
  apply propext
  apply forall_congr'
  intro i
  unfold quadraticPairGood quadraticPrescribedKernel
  simp only [transpose_one,one_mul,mul_one]
  have he : (1 : Mat (Port g i) (Port g i)).mulVecLin=LinearMap.id:=by
    ext x j
    simp
  rw [he,LinearMap.ker_id]
  rw [LinearMap.ker_eq_bot]
  rfl

theorem quadratic_many_frames (g : Route (I×J) G) (Q : GeoM g)
    (hN : ∀ i,2*num (Port g i)+2≤N) (u : ℝ) (hu : 0≤u)
    (P : I→Rack J N→Prop) (hp : ∀ i,bp (-u)≤pr unif (P i))
    (hd : peakExpense I J 1+(-(N:ℝ)/2+2*u)≤0) :
    pr (unifOn (quadraticIndependentNetwork g Q)) (fun x=>∀ i,P i (led i x)) ≤
      (4:ℝ)^Fintype.card G*bp (num I*num J*num J)*(num (I×J)+1)*
        ∏ i,pr unif (P i) := by
  let L:=fun i=>(1 : Mat (Port g i) (Port g i))
  have hL i : Surjective (L i).mulVec:=by
    intro x
    exact ⟨x,Matrix.one_mulVec x⟩
  have hz:=quadratic_network_exact_pos (N:=N) g L Q hL hN
  have hc:=quadratic_network_expansion_cost (N:=N) g L Q hL hN
  simp only [sub_self,Finset.sum_const_zero,mul_zero,bp_zero,mul_one] at hc
  rw [←quadratic_independent_exact] at hz hc
  let E:=crowded g
  let Z:=geoMatrix g Q
  let H:=∏ i,pr unif (P i)
  have hH : 0≤H:=Finset.prod_nonneg (fun _ _=>pr_nonneg unif_law.nz)
  have he (x : Rack (I×J) N) (hx : quadraticIndependentNetwork g Q x) :
      quadraticTraced E Z ((rackCoordinates (I×J) N).symm x):=by
    rw [quadratic_network_traced]
    intro i
    exact (hx i).2
  rw [←on_unif,pr_on]
  have hm:=pr_mono unif_law.nz (fun x (hx : quadraticIndependentNetwork g Q x ∧ ∀ i,P i (led i x))=>
    And.intro (he x hx.1) hx.2)
  have hf:=quadratic_repeated_flood E Z u hu P hp hd
  have hs : 0≤(num (I×J)+1)*bp (num I*num J*num J)*H:=by
    apply mul_nonneg _ hH
    exact mul_nonneg (by unfold num; positivity) (bp_pos _).le
  calc
    _≤(bp (-(dim (symmetricRail E):ℝ))*((num (I×J)+1)*bp (num I*num J*num J))*H)/
        pr unif (quadraticIndependentNetwork g Q):=div_le_div_of_nonneg_right (hm.trans hf) hz.le
    _=(bp (-(dim (symmetricRail E):ℝ))/pr unif (quadraticIndependentNetwork g Q))*
        ((num (I×J)+1)*bp (num I*num J*num J)*H):=by ring
    _≤(4:ℝ)^Fintype.card G*((num (I×J)+1)*bp (num I*num J*num J)*H):=
      mul_le_mul_of_nonneg_right hc hs
    _=_:=by ring

end
end Lax793645Proofs.Simplifications
