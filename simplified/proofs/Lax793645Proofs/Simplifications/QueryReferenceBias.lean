import Lax793645Proofs.Simplifications.GramReferenceBias
import Lax793645Proofs.Simplifications.QueryDensityRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

theorem query_reference_bias_calendar (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) :
    (Tendsto (fun n : ℕ=>2*bp (num (crowded (ownPort v.t)))*bp (-((M*n:ℕ):ℝ)/2))
      atTop (nhds 0)) ∧
    ∀ᶠ n : ℕ in atTop,∀ q : I→F,
      let ν:=unifOn (queryReferenceSet v q (M*n))
      IsLaw ν ∧ ∀ ξ : KeyCoordinates (KeySlots p v.t) (M*n),ξ≠0 →
        |avg ν (vectorPhase ξ)|≤2*bp (num (crowded (ownPort v.t)))*bp (-((M*n:ℕ):ℝ)/2) := by
  let E:=crowded (ownPort v.t)
  have hM' : 0<(M:ℝ)/2:=div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)) (by norm_num)
  have hv : Tendsto (fun n : ℕ=>bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    convert (bp_tendsto_zero hM').comp tendsto_natCast_atTop_atTop using 1
    funext n
    congr 1
    push_cast
    ring
  refine ⟨by simpa using hv.const_mul (2*bp (num E)),?_⟩
  filter_upwards [hv.eventually (eventually_le_nhds (half_pos (bp_pos (-num E))))] with n hn q ν
  let Z:=directions (ownPort v.t) (ownMap v.t q)
  have hK : queryReferenceSet v q (M*n)=gramKeySet E Z (M*n):=
    funext fun x=>propext (query_gram_equivalence v.t q x)
  have hh:=gram_reference_bias E Z hn
  rw [←hK] at hh
  exact ⟨hh.1,hh.2.2⟩

end
end Lax793645Proofs.Simplifications
