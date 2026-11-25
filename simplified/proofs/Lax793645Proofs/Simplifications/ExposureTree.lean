import Lax793645Proofs.Simplifications.MatchingFilters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section
variable {A S : Type*} [Fintype A] [Fintype S]

/-- The finite exposure argument for a mixture of nonconflicting unit laws.
Goodness is used only for counting retained emissions; the Bayesian laws are
never conditioned on the good-sample event. -/
theorem exposure_tree_impossible (H : Holes A) {μ : Wgt A} (hμ : IsLaw μ)
    {M D ε : ℝ} (hM : 0 < M) (hD : 0 < D) (hε : 0 < ε)
    (hsat : ∀ w, IsLaw w → pairCaps μ M D w → carried w H.unit →
      ε ≤ pr (pairW w w) (fun z => H.conflict z.1 z.2))
    (π : Wgt S) (K : S → Wgt (A × A)) (hπ : IsLaw π) (hK : ∀ s, IsLaw (K s))
    (hu : ∀ s, carried (K s) H.unit)
    (hc : ∀ s y x, H.conflict y x → K s y*K s x=0)
    (bad : S → Prop) (hbad : pr π bad < 1/8)
    (L b : ℕ) (hb : 0 < b) (hscale : D ≤ (2:ℝ)^b*(ε/32))
    (hbudget : 384*(b:ℝ) < (L:ℝ)*ε)
    (hgood : ∀ h : List (A × A), h.length ≤ L → ∀ s, ¬bad s →
      1/2 ≤ pr (K s) (retainedUnits μ M D (forecast (historyState π K h) K))) : False := by
  let ρ := historyState π K
  let σ h := forecast (ρ h) K
  let P h := retainedUnits μ M D (σ h)
  let α h := pr (σ h) (P h)
  let B h := pr (ρ h) bad
  let a (i : Fin b) := (2:ℝ)^i.val*(ε/32)
  let V h := clippedPotential (pairW μ μ) a (σ h)
  have hρ h : IsLaw (ρ h) := historyState_law hπ hK h
  have hσ h : IsLaw (σ h) := forecast_law (hρ h) hK
  have hcar h : carried (σ h) H.unit := by
    intro p hp
    change avg (ρ h) (fun s => K s p)=0
    simp only [hu _ p hp,avg_zero]
  have hα h (hh : h.length ≤ L) : 1/2-B h ≤ α h := by
    change _ ≤ avg (forecast (ρ h) K) (fun x => ind (P h x))
    rw [show forecast (ρ h) K=mixW (ρ h) K from rfl,mixW_avg]
    have hp (s : S) : 1/2-ind (bad s) ≤ pr (K s) (P h) := by
      by_cases hs : bad s
      · rw [ind_one hs]
        have hn := pr_nonneg (p:=P h) (hK s).nz
        linarith
      · rw [ind_zero hs,sub_zero]
        exact hgood h hh s hs
    have ha := avg_mono (hρ h).nz hp
    rwa [avg_sub,(hρ h).avg_const] at ha
  have hstep h (hh : h.length < L) :
      ε/192-ε/48*B h ≤ V h-avg (σ h) (fun y => V (y::h)) := by
    have hn : 0 ≤ V h-avg (σ h) (fun y => V (y::h)) :=
      forecast_drop_nonneg (pairW μ μ) a (hρ h) hK
    have hlarge (ha : 1/4 ≤ α h) : ε/64 ≤ V h-avg (σ h) (fun y => V (y::h)) := by
      have hr := retained_supersaturation hμ hM hD hε.le H hsat (hσ h) (hcar h) ha
      have hd := forecast_exposure (pairW μ μ) (ρ h) K (pairW_law hμ hμ) (hρ h) hK
        H.conflict hc (P h) (ε/32) D (by positivity) b hb hscale (fun x hx => by
          have hx' : σ h x ≤ D*pairW μ μ x/4 := le_of_not_gt hx.2.2
          have hm := mul_nonneg hD.le ((pairW_law hμ hμ).nz x)
          linarith)
      change _ ≤ V h-avg (σ h) (fun y => V (y::h)) at hd
      linarith
    have ha1 : α h ≤ 1 := (pr_le_tot (hσ h).nz).trans_eq (hσ h).total
    have hd := exposure_drop_from_retention hε.le ha1 hn hlarge
    have ha := hα h hh.le
    have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ ε/48 by positivity)
    linarith
  have hV h : 0 ≤ V h := (clippedPotential_bounds (pairW μ μ) (σ h) a
    (pairW_law hμ hμ).nz (hσ h) (fun i => by dsimp [a]; positivity)).1
  have hB h : avg (σ h) (fun y => B (y::h))=B h :=
    bayes_average (hρ h) hK (fun s => ind (bad s))
  have ht := tree_budget σ hσ V B hV (ε/192) (ε/48) L hB hstep
  have hv : V [] ≤ b := by
    simpa only [Fintype.card_fin] using (clippedPotential_bounds (pairW μ μ) (σ []) a
      (pairW_law hμ hμ).nz (hσ []) (fun i => by dsimp [a]; positivity)).2
  have hb0 : B [] < 1/8 := hbad
  have hm := mul_le_mul_of_nonneg_left (show ε/384 ≤ ε/192-ε/48*B [] by nlinarith) (Nat.cast_nonneg L)
  nlinarith

end
end Lax793645Proofs.Simplifications
