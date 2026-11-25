import Lax793645Proofs.Simplifications.RestrictedSuperlevels
import Lax793645Proofs.Simplifications.SuccessfulProductPartitions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
variable {A B : Type} [Fintype A] [Fintype B]

/-- L1 error of measures is exactly weighted L1 error of their densities.
Only the measure being reconstructed needs reference support. -/
theorem var_one_density_reconstruction (ν x g : Wgt A) (hν : ∀ a,0≤ν a)
    (hx : lsupp x ν) :
    varOne x (fun a=>ν a*g a)=lcost ν (density ν x) g := by
  unfold varOne lcost avg
  apply Finset.sum_congr rfl
  intro a _
  have he : ν a*density ν x a=x a := by
    by_cases h : x a=0
    · simp [density,h]
    · unfold density
      exact mul_div_cancel₀ _ (hx a h)
  rw [←abs_of_nonneg (hν a),←abs_mul,mul_sub,he]

theorem pr_supported_congr (x ν : Wgt A) (hx : lsupp x ν)
    (P Q : A→Prop) (h : ∀ a,ν a≠0 → (P a↔Q a)) : pr x P=pr x Q := by
  apply avg_congr
  intro a ha
  exact congrArg ind (propext (h a (hx a ha)))

/-- The linear cell test can ignore reference-zero keys. It agrees with
the density superlevel on every actual successful-query support. -/
theorem projected_superlevel_pr (x ν : Wgt A) (hν : ∀ a,0≤ν a)
    (hx : lsupp x ν) (P : A→B) (φ : Wgt B) (E : A→Prop) (t : ℝ) :
    pr x (fun a=>E a ∧ 2*t≤φ (P a))=
      pr x (fun a=>E a ∧ cliff ν (fun a=>ν a*φ (P a)) t a) := by
  apply pr_supported_congr x ν hx
  intro a ha
  have hp : 0<ν a:=lt_of_le_of_ne (hν a) (Ne.symm ha)
  change (E a ∧ 2*t≤φ (P a)) ↔ (E a ∧ 2*t*ν a≤ν a*φ (P a))
  rw [mul_comm (2*t) (ν a),mul_le_mul_iff_right₀ hp]

end
end Lax793645Proofs.Simplifications
