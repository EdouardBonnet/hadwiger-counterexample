import Lax793645Proofs.Simplifications.FiniteBayes
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.DensityCaps
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SampledGraphs

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section
variable {A X : Type*} [Fintype A] [Fintype X]

def heavyEndpoints (μ : Wgt A) (M : ℝ) (σ : Wgt (A × A)) (x : A) : Prop :=
  M*μ x/4 < mapW σ Prod.fst x ∨ M*μ x/4 < mapW σ Prod.snd x

def heavyPairs (μ : Wgt A) (D : ℝ) (σ : Wgt (A × A)) (p : A × A) : Prop :=
  D*pairW μ μ p/4 < σ p

def retainedUnits (μ : Wgt A) (M D : ℝ) (σ : Wgt (A × A)) (p : A × A) : Prop :=
  ¬ heavyEndpoints μ M σ p.1 ∧ ¬ heavyEndpoints μ M σ p.2 ∧ ¬ heavyPairs μ D σ p

theorem heavy_mass (q w : Wgt X) (hw : IsLaw w) {c : ℝ} (hc : 0 < c) :
    pr q (fun x => c*q x < w x) ≤ 1/c := by
  apply (le_div_iff₀ hc).mpr
  rw [mul_comm,pr,avg,Finset.mul_sum]
  calc
    (∑ x, c*(q x*ind (c*q x < w x))) ≤ ∑ x, w x := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : c*q x < w x
      · rw [ind_one h,mul_one]; exact h.le
      · rw [ind_zero h,mul_zero,mul_zero]; exact hw.nz x
    _ = 1 := hw.total

theorem heavyEndpoints_mass {μ : Wgt A} (hμ : IsLaw μ) {M : ℝ} (hM : 0 < M)
    {σ : Wgt (A × A)} (hσ : IsLaw σ) : pr μ (heavyEndpoints μ M σ) ≤ 8/M := by
  have h₁ := heavy_mass μ (mapW σ Prod.fst) (mapW_law hσ _) (div_pos hM (by norm_num : (0:ℝ)<4))
  have h₂ := heavy_mass μ (mapW σ Prod.snd) (mapW_law hσ _) (div_pos hM (by norm_num : (0:ℝ)<4))
  simp only [div_mul_eq_mul_div,one_div_div] at h₁ h₂
  exact (pr_or_le hμ.nz).trans (by convert add_le_add h₁ h₂ using 1 <;> ring)

theorem heavyPairs_mass {μ : Wgt A} {D : ℝ} (hD : 0 < D)
    {σ : Wgt (A × A)} (hσ : IsLaw σ) : pr (pairW μ μ) (heavyPairs μ D σ) ≤ 4/D := by
  change pr (pairW μ μ) (fun p => D*pairW μ μ p/4 < σ p) ≤ 4/D
  simpa only [div_mul_eq_mul_div,one_div_div] using
    heavy_mass (pairW μ μ) σ hσ (div_pos hD (by norm_num : (0:ℝ)<4))

theorem restricted_map_cap {w : Wgt X} (hw : IsLaw w) (P : X → Prop)
    (f : X → A) (v : Wgt A) (hv : ∀ a, 0 ≤ v a)
    (hcap : ∀ x, P x → mapW w f (f x) ≤ v (f x)/4)
    (hα : 1/4 ≤ pr w P) : ∀ a, mapW (normW (subW w P)) f a ≤ v a := by
  intro a
  change pr (normW (subW w P)) (fun x => f x=a) ≤ v a
  rw [pr,avg_norm,subW_tot]
  apply (div_le_iff₀ (by linarith : 0 < pr w P)).mpr
  by_cases hx : ∃ x, P x ∧ f x=a
  · obtain ⟨x,hx,hf⟩ := hx
    have hc : mapW w f a ≤ v a/4 := by simpa only [hf] using hcap x hx
    have hs : avg (subW w P) (fun x => ind (f x=a)) ≤ mapW w f a :=
      avg_mono_left (fun _ => ind_nonneg _) (subW_le hw.nz P)
    have hm := mul_le_mul_of_nonneg_left hα (hv a)
    linarith
  · have hz : avg (subW w P) (fun x => ind (f x=a))=0 := by
      unfold avg subW
      apply Finset.sum_eq_zero
      intro x _
      by_cases hp : P x
      · have hf : f x ≠ a := fun hf => hx ⟨x,hp,hf⟩
        simp only [ind_zero hf,mul_zero]
      · rw [ind_zero hp,mul_zero,zero_mul]
    rw [hz]
    exact mul_nonneg (hv a) (pr_nonneg hw.nz)

theorem retained_caps {μ : Wgt A} (hμ : IsLaw μ) {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    {σ : Wgt (A × A)} (hσ : IsLaw σ) (hα : 1/4 ≤ pr σ (retainedUnits μ M D σ)) :
    pairCaps μ M D (normW (subW σ (retainedUnits μ M D σ))) := by
  let P := retainedUnits μ M D σ
  refine ⟨restricted_map_cap hσ P Prod.fst (fun a => M*μ a)
      (fun a => mul_nonneg hM.le (hμ.nz a)) (fun x hx => ?_) hα,
    restricted_map_cap hσ P Prod.snd (fun a => M*μ a)
      (fun a => mul_nonneg hM.le (hμ.nz a)) (fun x hx => ?_) hα, ?_⟩
  · exact le_of_not_gt (fun h => hx.1 (Or.inl h))
  · exact le_of_not_gt (fun h => hx.2.1 (Or.inr h))
  · intro p
    change subW σ P p / pr σ P ≤ D*pairW μ μ p
    apply (div_le_iff₀ (by linarith : 0 < pr σ P)).mpr
    by_cases hp : P p
    · rw [subW,ind_one hp,mul_one]
      have hc : σ p ≤ D*pairW μ μ p/4 := le_of_not_gt hp.2.2
      have hm := mul_le_mul_of_nonneg_left hα (mul_nonneg hD.le ((pairW_law hμ hμ).nz p))
      linarith
    · rw [subW,ind_zero hp,mul_zero]
      exact mul_nonneg (mul_nonneg hD.le ((pairW_law hμ hμ).nz p)) (pr_nonneg hσ.nz)

theorem retained_normal_conflict (σ : Wgt X) (P : X → Prop) (C : X → X → Prop) :
    pr (pairW (normW (subW σ P)) (normW (subW σ P))) (fun z => C z.2 z.1) =
      retainedConflict σ P C / (pr σ P)^2 := by
  classical
  change (∑ z : X × X, (subW σ P z.1/pr σ P)*(subW σ P z.2/pr σ P)*ind (C z.2 z.1)) = _
  rw [Fintype.sum_prod_type]
  unfold retainedConflict
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  simp only [subW,ind_and]
  ring

theorem retained_supersaturation {μ : Wgt A} (hμ : IsLaw μ) {M D ε : ℝ}
    (hM : 0 < M) (hD : 0 < D) (hε : 0 ≤ ε) (H : Holes A)
    (hsat : ∀ w, IsLaw w → pairCaps μ M D w → carried w H.unit →
      ε ≤ pr (pairW w w) (fun z => H.conflict z.1 z.2))
    {σ : Wgt (A × A)} (hσ : IsLaw σ) (hu : carried σ H.unit)
    (hα : 1/4 ≤ pr σ (retainedUnits μ M D σ)) :
    ε/16 ≤ retainedConflict σ (retainedUnits μ M D σ) H.conflict := by
  let P := retainedUnits μ M D σ
  have hpos : 0 < pr σ P := by linarith
  have hs := hsat (normW (subW σ P))
    (normW_law (subW_nonneg hσ.nz P) hpos)
    (retained_caps hμ hM hD hσ hα)
    (normW_carried (fun p hp => by rw [subW,hu p hp,zero_mul]))
  have he : (fun z : (A × A) × (A × A) => H.conflict z.1 z.2)=
      (fun z => H.conflict z.2 z.1) := by
    funext z
    apply propext
    constructor <;> intro hz <;>
      exact ⟨H.sym hz.1,H.sym hz.2.2.1,H.sym hz.2.1,H.sym hz.2.2.2⟩
  rw [he,retained_normal_conflict] at hs
  have hb := (le_div_iff₀ (sq_pos_of_pos hpos)).mp hs
  have hm := mul_le_mul_of_nonneg_left (show (1:ℝ)/16 ≤ (pr σ P)^2 by nlinarith [sq_nonneg (pr σ P-1/4)]) hε
  linarith

end
end Lax793645Proofs.Simplifications
