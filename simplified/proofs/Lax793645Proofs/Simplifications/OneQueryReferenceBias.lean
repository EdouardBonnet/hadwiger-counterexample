import Lax793645Proofs.Simplifications.QuadraticReferenceFourier
import Lax793645Proofs.Simplifications.OneQueryDensityRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

theorem one_query_reference_bias_calendar (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) :
    (Tendsto (fun n : ℕ=>2*bp (quadraticReferenceCost (crowded (ownPort v.t)))*bp (-((M*n:ℕ):ℝ)/2))
      atTop (nhds 0)) ∧
    ∀ᶠ n : ℕ in atTop,∀ q : I→F,
      let ν:=unifOn (oneQueryReferenceSet v q (M*n))
      IsLaw ν ∧ ∀ ξ : KeyCoordinates (KeySlots p v.t) (M*n),ξ≠0 →
        |avg ν (vectorPhase ξ)|≤2*bp (quadraticReferenceCost (crowded (ownPort v.t)))*bp (-((M*n:ℕ):ℝ)/2) := by
  let E:=crowded (ownPort v.t)
  have hM' : 0<(M:ℝ)/2:=div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)) (by norm_num)
  have hv : Tendsto (fun n : ℕ=>bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    convert (bp_tendsto_zero hM').comp tendsto_natCast_atTop_atTop using 1
    funext n
    congr 1
    push_cast
    ring
  refine ⟨by simpa using hv.const_mul (2*bp (quadraticReferenceCost E)),?_⟩
  filter_upwards [hv.eventually (eventually_le_nhds (half_pos (bp_pos (-quadraticReferenceCost E))))] with n hn q ν
  let Z:=geoMatrix (ownPort v.t) (ownMap v.t q)
  have hK : oneQueryReferenceSet v q (M*n)=quadraticTraced E Z (N:=M*n):=
    rfl
  have hh:=quadratic_reference_bias E Z hn
  rw [←hK] at hh
  exact ⟨hh.1,hh.2.2⟩

end
end Lax793645Proofs.Simplifications
