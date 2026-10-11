import Lax342547.FourPhaseParity
import Lax342547Proofs.FourierTests
import Lax342547Proofs.TinyCompatibility

namespace Lax342547Proofs.FourPhaseParity
open Lax342547.FourPhaseParity

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.FourierTests
open Lax342547.RelativeEntropy Lax342547.CellAveraging
open scoped BigOperators

/--
---
conclusion: Lax342547.FourPhaseParity.phase_duplicate
---
-/
theorem phase_duplicate (t : Fin 2 → Binary) (b : Fin 4 → Binary) :
    phase (duplicate t) b = phase t (parity b) := by
  unfold phase dotProduct duplicate parity
  congr 1
  simp [Fin.sum_univ_four,Fin.sum_univ_two]
  ring

/--
---
conclusion: Lax342547.FourPhaseParity.duplicate_injective
---
-/
theorem duplicate_injective : Function.Injective duplicate := by
  intro t u h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 2

/--
---
conclusion: Lax342547.FourPhaseParity.even_iff_duplicate
---
-/
theorem even_iff_duplicate (t : Fin 4 → Binary) :
    Lax342547.FourPhaseParity.Even t ↔ ∃ s, duplicate s = t := by
  constructor
  · rintro ⟨h₀,h₁⟩
    refine ⟨![t 0,t 2],?_⟩
    funext i
    fin_cases i <;> simp [duplicate,h₀,h₁]
  · rintro ⟨s,rfl⟩
    simp [Lax342547.FourPhaseParity.Even,duplicate]

/--
---
conclusion: Lax342547.FourPhaseParity.even_character_sum
---
-/
theorem even_character_sum {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (bits : Ω → Fin 4 → Binary) :
    (∑ t ∈ Finset.univ.filter Lax342547.FourPhaseParity.Even, characterMean ρ bits 0 t) =
      4*patternMass ρ (fun ω => parity (bits ω)) 0 := by
  classical
  have he : Finset.univ.filter Lax342547.FourPhaseParity.Even = Finset.univ.image duplicate := by
    ext t
    simp [even_iff_duplicate]
  rw [he,Finset.sum_image (fun t _ u _ h => duplicate_injective h)]
  have hmean (t : Fin 2 → Binary) : characterMean ρ bits 0 (duplicate t) =
      characterMean ρ (fun ω => parity (bits ω)) 0 t := by
    unfold characterMean
    apply Finset.sum_congr rfl
    intro ω _
    rw [phase_duplicate]
    simp [phase,Lax342547Proofs.Walsh.sign_zero]
  simp only [hmean]
  have hh := Lax342547Proofs.FourierTests.pattern_inversion ρ (fun ω => parity (bits ω)) 0
  norm_num only [Fintype.card_fin] at hh
  exact hh

/--
---
conclusion: Lax342547.FourPhaseParity.odd_character_card
---
-/
theorem odd_character_card : (Finset.univ.filter (fun t : Fin 4 → Binary => ¬ Lax342547.FourPhaseParity.Even t)).card = 12 := by
  decide

/--
---
conclusion: Lax342547.FourPhaseParity.four_phase_parity_lower
---
-/
theorem four_phase_parity_lower {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (bits : Ω → Fin 4 → Binary) (ε : ℝ)
    (hodd : ∀ t, ¬ Lax342547.FourPhaseParity.Even t → |characterMean ρ bits 0 t| ≤ ε) :
    patternMass ρ (fun ω => parity (bits ω)) 0/4-3*ε/4 ≤ patternMass ρ bits 0 := by
  classical
  have ho : -12*ε ≤ ∑ t ∈ Finset.univ.filter (fun t => ¬ Lax342547.FourPhaseParity.Even t),characterMean ρ bits 0 t := by
    have hs := Finset.sum_le_sum (s := Finset.univ.filter (fun t => ¬ Lax342547.FourPhaseParity.Even t))
      (fun t ht => (abs_le.mp (hodd t (Finset.mem_filter.mp ht).2)).1)
    simpa only [Finset.sum_const,nsmul_eq_mul,odd_character_card,Nat.cast_ofNat,neg_mul,mul_neg] using hs
  have hs := Finset.sum_filter_add_sum_filter_not (s := Finset.univ) Lax342547.FourPhaseParity.Even (fun t => characterMean ρ bits 0 t)
  rw [even_character_sum,Lax342547Proofs.FourierTests.pattern_inversion] at hs
  norm_num only [Fintype.card_fin] at hs
  linarith

/--
---
conclusion: Lax342547.FourPhaseParity.tiny_four_phase_lower
---
-/
theorem tiny_four_phase_lower {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (bits : Ω × Ω → Fin 4 → Binary) (d N : ℕ) (ε : ℝ)
    (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) (hrank : F.rank ≤ d*N)
    (hparity : ∀ a b, parity (bits (a,b)) = ![F a b,F b a])
    (hodd : ∀ t, ¬ Lax342547.FourPhaseParity.Even t → |characterMean (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0 t| ≤ ε) :
    1/(16*(1+(d : ℝ)*N)^4)-3*ε/4 ≤
      patternMass (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0 := by
  classical
  have hp : patternMass (fun ab : Ω × Ω => μ ab.1*μ ab.2) (fun ab => parity (bits ab)) 0 =
      pairEventMass μ μ (fun a b => F a b = 0 ∧ F b a = 0) := by
    unfold patternMass pairEventMass
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    simp only [hparity]
    have he : (![F a b,F b a] : Fin 2 → Binary) = 0 ↔ F a b = 0 ∧ F b a = 0 := by
      constructor
      · intro h
        exact ⟨congrFun h 0,congrFun h 1⟩
      · rintro ⟨h₀,h₁⟩
        funext i
        fin_cases i <;> simp [h₀,h₁]
    simp only [he]
    split_ifs <;> simp
  have hc := Lax342547Proofs.TinyCompatibility.tiny_compatible_mass_rank_bound μ F d N hμ hdiag hrank
  have hl := four_phase_parity_lower (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits ε hodd
  rw [hp] at hl
  have ht := div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 4)
  have he : (1/(4*(1+(d : ℝ)*N)^4))/4 = 1/(16*(1+(d : ℝ)*N)^4) := by rw [div_div]; congr 1; ring
  rw [he] at ht
  linarith

/--
---
conclusion: Lax342547.FourPhaseParity.tiny_four_phase_positive
---
-/
theorem tiny_four_phase_positive {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (bits : Ω × Ω → Fin 4 → Binary) (d N : ℕ) (ε : ℝ)
    (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) (hrank : F.rank ≤ d*N)
    (hparity : ∀ a b, parity (bits (a,b)) = ![F a b,F b a])
    (hodd : ∀ t, ¬ Lax342547.FourPhaseParity.Even t → |characterMean (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0 t| ≤ ε)
    (hε : ε ≤ 1/(24*(1+(d : ℝ)*N)^4)) :
    1/(32*(1+(d : ℝ)*N)^4) ≤
      patternMass (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0 := by
  have hl := tiny_four_phase_lower μ F bits d N ε hμ hdiag hrank hparity hodd
  have he : 1/(16*(1+(d : ℝ)*N)^4)-3*(1/(24*(1+(d : ℝ)*N)^4))/4 =
      1/(32*(1+(d : ℝ)*N)^4) := by
    have hz : (1+(d : ℝ)*N)^4 ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [← he]
  linarith

end Lax342547Proofs.FourPhaseParity
