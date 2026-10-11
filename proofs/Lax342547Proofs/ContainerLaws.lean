import Lax342547.ContainerLaws
import Lax342547Proofs.UnitLaws

namespace Lax342547Proofs.ContainerLaws
open Lax342547.ContainerLaws

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.ContainerLaws.residual_mono
---
-/
theorem residual_mono {U : Type} [Fintype U] (P : Set (U → ℝ)) (R T : Finset U)
    (hTR : T ⊆ R) : residual P T ⊆ residual P R := by
  rintro ρ ⟨hP,hT⟩
  exact ⟨hP,fun x hx => hT x (fun h => hx (hTR h))⟩

/--
---
conclusion: Lax342547.ContainerLaws.residual_compact
---
-/
theorem residual_compact {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U)
    (hP : IsCompact P) : IsCompact (residual P R) := by
  classical
  have hc : IsClosed {ρ : U → ℝ | ∀ x, x ∉ R → ρ x = 0} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_apply x) continuous_const
  exact hP.inter_right hc

/--
---
conclusion: Lax342547.ContainerLaws.residual_convex
---
-/
theorem residual_convex {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U)
    (hP : Convex ℝ P) : Convex ℝ (residual P R) := by
  intro ρ hρ σ hσ a b ha hb hab
  refine ⟨hP hρ.1 hσ.1 ha hb hab,?_⟩
  intro x hx
  simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hρ.2 x hx,hσ.2 x hx]

/--
---
conclusion: Lax342547.ContainerLaws.supported_mass
---
-/
theorem supported_mass {U : Type} [Fintype U] (ρ : U → ℝ) (R : Finset U)
    (hρ : Probability ρ) (hs : ∀ x, x ∉ R → ρ x = 0) : cellMass ρ (fun x => x ∈ R) = 1 := by
  classical
  unfold cellMass
  calc
    _ = ∑ x, ρ x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ R
      · simp [hx]
      · simp [hx,hs x hx]
    _ = 1 := hρ.2

/--
---
conclusion: Lax342547.ContainerLaws.positive_support
---
-/
theorem positive_support {U : Type} [Fintype U] (ρ : U → ℝ) (hρ : Probability ρ) :
    ∃ x, 0 < ρ x := by
  by_contra hn
  push Not at hn
  have hh : (∑ x, ρ x) ≤ 0 := Finset.sum_nonpos (fun x _ => hn x)
  rw [hρ.2] at hh
  norm_num at hh

/--
---
conclusion: Lax342547.ContainerLaws.mass_complement
---
-/
theorem mass_complement {U : Type} [Fintype U] (ρ : U → ℝ) (S : U → Prop)
    (hρ : Probability ρ) : cellMass ρ (fun x => ¬ S x) = 1-cellMass ρ S := by
  classical
  have h : cellMass ρ (fun x => ¬ S x)+cellMass ρ S = 1 := by
    unfold cellMass
    rw [← Finset.sum_add_distrib]
    convert hρ.2 using 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : S x <;> simp [hx]
  linarith

/--
---
conclusion: Lax342547.ContainerLaws.support_mass_positive
---
-/
theorem support_mass_positive {U : Type} [Fintype U]
    (ρ σ : U → ℝ) (S : U → Prop) (hρ : Probability ρ) (hσ : Probability σ)
    (hs : ∀ x, ¬ S x → σ x = 0) (hfull : ∀ x, 0 < σ x → 0 < ρ x) :
    0 < cellMass ρ S := by
  classical
  obtain ⟨x,hx⟩ := positive_support σ hσ
  have hS : S x := by
    by_contra hn
    rw [hs x hn] at hx
    exact lt_irrefl 0 hx
  unfold cellMass
  apply Finset.sum_pos'
  · intro y _
    split_ifs
    · exact hρ.1 y
    · exact le_rfl
  · refine ⟨x,Finset.mem_univ x,?_⟩
    simpa [hS] using hfull x hx

/--
---
conclusion: Lax342547.ContainerLaws.heavy_neighbor
---
-/
theorem heavy_neighbor {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop)
    (R : Finset U) (ε : ℝ) (hρ : Probability ρ) (hs : ∀ x, x ∉ R → ρ x = 0)
    (_hε : 0 < ε) (hmass : ε ≤ conflictMass ρ H) :
    ∃ v ∈ R, ε ≤ neighborMass ρ H v := by
  classical
  by_contra hn
  push Not at hn
  have hlt : conflictMass ρ H < ∑ v, ρ v*ε := by
    unfold conflictMass
    apply Finset.sum_lt_sum
    · intro v _
      by_cases hv : v ∈ R
      · exact mul_le_mul_of_nonneg_left (hn v hv).le (hρ.1 v)
      · simp [hs v hv]
    · obtain ⟨v,hv⟩ := positive_support ρ hρ
      have hvR : v ∈ R := by
        by_contra hnR
        rw [hs v hnR] at hv
        exact lt_irrefl 0 hv
      exact ⟨v,Finset.mem_univ v,mul_lt_mul_of_pos_left (hn v hvR) hv⟩
  rw [← Finset.sum_mul,hρ.2,one_mul] at hlt
  exact (not_lt_of_ge hmass) hlt

/--
---
conclusion: Lax342547.ContainerLaws.minimum_mono
---
-/
theorem minimum_mono {U : Type} [Fintype U] (P : Set (U → ℝ)) (q ρ σ : U → ℝ)
    (R T : Finset U) (hTR : T ⊆ R) (hσ : σ ∈ residual P T)
    (hmin : ∀ τ ∈ residual P R, entropy ρ q ≤ entropy τ q) : entropy ρ q ≤ entropy σ q := by
  exact hmin σ (residual_mono P R T hTR hσ)

/--
---
conclusion: Lax342547.ContainerLaws.recording_entropy_increment
---
-/
theorem recording_entropy_increment {U : Type} [Fintype U]
    (P : Set (U → ℝ)) (q ρ σ : U → ℝ) (R : Finset U) (H : U → U → Prop) (v : U) (ε : ℝ)
    (hprob : ∀ τ ∈ P, Probability τ) (hconv : Convex ℝ P)
    (hρ : ρ ∈ residual P R) (hmin : ∀ τ ∈ residual P R, entropy ρ q ≤ entropy τ q)
    (hσ : σ ∈ residual P R ∧ ∀ x, H v x → σ x = 0)
    (_hε : ε < 1) (hheavy : ε ≤ neighborMass ρ H v) :
    -Real.log (1-ε) ≤ entropy σ q-entropy ρ q := by
  have hpr : ∀ τ ∈ residual P R, Probability τ := fun τ hτ => hprob τ hτ.1
  have hc := residual_convex P R hconv
  have hfull := Lax342547Proofs.EntropyProjection.minimizer_full_support
    (residual P R) q ρ hpr hc hρ hmin σ hσ.1
  have hpos := support_mass_positive ρ σ (fun x => ¬ H v x) (hprob ρ hρ.1)
    (hprob σ hσ.1.1) (by simpa using hσ.2) hfull
  have hcost := Lax342547Proofs.EntropyProjection.projection_support_cost
    (residual P R) q ρ hpr hc hρ hmin σ hσ.1 (fun x => ¬ H v x)
    (by simpa using hσ.2) hpos
  have hmass : cellMass ρ (fun x => ¬ H v x) ≤ 1-ε := by
    rw [mass_complement ρ (H v) (hprob ρ hρ.1)]
    exact sub_le_sub_left hheavy 1
  have hlog := Real.log_le_log hpos hmass
  linarith

end Lax342547Proofs.ContainerLaws
