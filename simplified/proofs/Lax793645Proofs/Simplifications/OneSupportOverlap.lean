import Lax793645Proofs.Simplifications.OneSupportScores

/-! The direct projection inequality transfers support overlap using only one-sided projected errors. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace OneTypus
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates}
variable (w : Typus p q d e) (μ ρ : Wgt (OneUnit p n N))
  (F G : OneUnit p n N→Prop) (s : Charts p n d) (t : Charts p n e)
  (m : Mixer p n) (Y : OneSilhouette p N r) (θ : ℝ)

theorem one_support_overlap_scale :
    (θ^Fintype.card (Messenger q))^2*
      dip (oneLawNu p N w.t w.z) (OneQuill.oneSupportShowcase w.qA w.t w.z m s Y μ F 1)
        (OneQuill.oneSupportShowcase w.qB w.t w.z m t Y ρ G 1)≤
      dip (oneLawNu p N w.t w.z)
        (OneQuill.oneSupportShowcase w.qA w.t w.z m s Y μ F θ)
        (OneQuill.oneSupportShowcase w.qB w.t w.z m t Y ρ G θ) := by
  unfold dip
  rw [←avg_mul']
  apply le_of_eq
  apply avg_congr
  intro x _
  rw [OneQuill.one_support_showcase_scale w.qA w.t w.z m s Y μ F θ,
    OneQuill.one_support_showcase_scale w.qB w.t w.z m t Y ρ G θ]
  ring

theorem one_support_projected_mend {A : Type} [Fintype A]
    (P : KeyCoordinates (KeySlots p w.t) N→A)
    (hθ : 0≤θ ∧ θ≤1) (hμ : IsLaw μ) (hρ : IsLaw ρ)
    (hν : IsLaw (unifOn (oneOwnPart (N:=N) w.t w.z))) :
    let ν:=unifOn (oneOwnPart (N:=N) w.t w.z)
    let QA:=oneSales w.qA w.t w.z μ F m s
    let QB:=oneSales w.qB w.t w.z ρ G m t
    dip (oneLawNu p N w.t w.z)
      (OneQuill.oneSupportShowcase w.qA w.t w.z m s Y μ F θ)
      (OneQuill.oneSupportShowcase w.qB w.t w.z m t Y ρ G θ)^2≤
      dip ν (banner ν P (density ν QA)) (banner ν P (density ν QB))+
        (OneQuill.oneSupportProjectedLoss w.qA w.t w.z m s Y μ F θ P+
          OneQuill.oneSupportProjectedLoss w.qB w.t w.z m t Y ρ G θ P) := by
  intro ν QA QB
  let f:=OneQuill.oneSupportShowcase w.qA w.t w.z m s Y μ F θ
  let g:=OneQuill.oneSupportShowcase w.qB w.t w.z m t Y ρ G θ
  let E:=oneQueryCoordinateEquiv w.t N
  have hf:=OneQuill.one_support_showcase_bound w.qA w.t w.z m s Y μ F θ hθ hμ
  have hg:=OneQuill.one_support_showcase_bound w.qB w.t w.z m t Y ρ G θ hθ hρ
  have hh:=one_sided_projected_mend ν hν P (f∘E) (g∘E) (density ν QA) (density ν QB)
    ⟨fun x=>hf.1 _,fun x=>hf.2 _⟩ ⟨fun x=>hg.1 _,fun x=>hg.2 _⟩
    (fun x=>div_nonneg (one_sales_nonneg w.qA w.t w.z μ F m s hμ.nz x) (hν.nz x))
    (fun x=>div_nonneg (one_sales_nonneg w.qB w.t w.z ρ G m t hρ.nz x) (hν.nz x))
  change dip (unifOn (oneOwnPart w.t w.z)) (f∘oneQueryCoordinateEquiv w.t N)
    (g∘oneQueryCoordinateEquiv w.t N)^2≤_ at hh
  rw [one_reference_dip] at hh
  simpa only [OneQuill.oneSupportProjectedLoss,f,g,E,add_assoc] using hh

end OneTypus

end
end Lax793645Proofs.Simplifications
