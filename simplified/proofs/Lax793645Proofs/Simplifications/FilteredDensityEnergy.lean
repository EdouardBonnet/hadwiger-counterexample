import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C J : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype J]

def densityFamilyEnergy (ν : Wgt A) (μ : Wgt J) (d : J→Wgt A) (P : A→B) : ℝ :=
  avg μ (fun i=>ode ν (banner ν P (d i)))

theorem projection_self_adjoint (ν : Wgt A) (hν : ∀ x,0≤ν x)
    (P : A→B) (f g : Wgt A) :
    dip ν (banner ν P f) g=dip ν f (banner ν P g) := by
  have h1:=cash_orth ν hν P f (cashbook ν P g)
  have h2:=cash_orth ν hν P g (cashbook ν P f)
  change dip ν (banner ν P f) (banner ν P g)=dip ν f (banner ν P g) at h1
  change dip ν (banner ν P g) (banner ν P f)=dip ν g (banner ν P f) at h2
  rw [dip_sym ν (banner ν P g),dip_sym ν g] at h2
  exact h2.symm.trans h1

theorem dip_density_mixture (ν : Wgt A) (t : Wgt J) (d : J→Wgt A) (f : Wgt A) :
    dip ν (mixW t d) f=avg t (fun i=>dip ν (d i) f) := by
  unfold dip mixW
  simp_rw [←avg_mul]
  exact avg_avg _ _ _

theorem filtered_projection_discrepancy (ν : Wgt A) (hν : ∀ x,0≤ν x)
    (t : Wgt J) (d : J→Wgt A) (P : A→B) (f : Wgt A) :
    dip ν (fun x=>mixW t d x-banner ν P (mixW t d) x) f=
      avg t (fun i=>dip ν (fun x=>d i x-banner ν P (d i) x) f) := by
  rw [dip_sub,projection_self_adjoint ν hν,dip_density_mixture,dip_density_mixture,←avg_sub]
  apply avg_congr
  intro i _
  rw [dip_sub,projection_self_adjoint ν hν]

/-- A single energy controls every filtered member of the family. The
choice of filter can subsequently depend on an independently drawn leaf. -/
theorem filtered_density_gain (ν : Wgt A) (hν : SubLaw ν)
    (μ : Wgt J) (hμ : SubLaw μ) (d : J→Wgt A) (t : Wgt J)
    (ht : ∀ i,0≤t i) (hcap : ∀ i,t i≤μ i)
    (P : A→B) (Q : B→C) (f : Wgt B) (hf : ∀ x,|f (P x)|≤1) :
    (dip ν (fun x=>mixW t d x-banner ν (Q∘P) (mixW t d) x) (f∘P))^2≤
      densityFamilyEnergy ν μ d P-densityFamilyEnergy ν μ d (Q∘P) := by
  let Z i:=dip ν (fun x=>d i x-banner ν (Q∘P) (d i) x) (f∘P)
  rw [filtered_projection_discrepancy ν hν.nz]
  have htotal : tot t≤1:=(Finset.sum_le_sum (fun i _=>hcap i)).trans hμ.total
  have hcs:=avg_CS ht Z (fun _=>1)
  simp only [mul_one,one_pow,avg_const,mul_one] at hcs
  have hsq : avg t (fun i=>Z i^2)*tot t≤avg t (fun i=>Z i^2):=
    (mul_le_mul_of_nonneg_left htotal (avg_nonneg ht (fun i=>sq_nonneg _))).trans_eq (mul_one _)
  have hweight : avg t (fun i=>Z i^2)≤avg μ (fun i=>Z i^2):=
    avg_mono_left (fun i=>sq_nonneg _) hcap
  have hgain:=avg_mono hμ.nz (fun i=>archive_gain hν (d i) P Q f hf)
  rw [avg_sub] at hgain
  exact hcs.trans (hsq.trans (hweight.trans hgain))

/-- Orthogonal projection of the test onto a refinement preserves its
pairing with every density measurable on the old partition. -/
theorem refinement_test_orthogonal (ν : Wgt A) (hν : ∀ x,0≤ν x)
    (P : A→B) (Q : B→C) (d f : Wgt A) :
    dip ν (banner ν (Q∘P) d) (banner ν P f)=dip ν (banner ν (Q∘P) d) f := by
  rw [dip_sym ν _ (banner ν P f),dip_sym ν _ f]
  exact cash_orth ν hν P f (cashbook ν (Q∘P) d∘Q)

end
end Lax793645Proofs.Simplifications
