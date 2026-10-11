import Lax342547.UniformTableInjection
import Lax342547Proofs.PreparedInjection
import Lax342547Proofs.PreparedInjectionScale

namespace Lax342547Proofs.UniformTableInjection

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.PreparedInjection
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.UniformTableInjection.exists_uniform_injection
---
-/
theorem exists_uniform_injection {Comp : Type} [Fintype Comp] [Nonempty Comp]
    (K Cs : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ,∀ c : ℕ,∃ N₀ : ℕ,∀ N p m : ℕ,N₀ ≤ N → p ≤ N/8 → m ≤ N/100 →
      ∀ (U I : Type) [Fintype U] [Fintype I] (E : Matrix (Fin p) (Fin p) Binary)
      [Nonempty (Frame (Fin p) (Fin h) (Fin N) E)]
      (ρ : U → ℝ) (P : U → Pin (Comp × Bool) (Fin 2 × (Fin p ⊕ Fin h)) (Fin N))
      (A : U → Fin 2 → Comp → Frame (Fin p) (Fin h) (Fin N) E)
      (accept : U → U → Prop) (CL CR : I → U → Prop) (keyL keyR : U → I)
      (T : ∀ a b,Table (P a) (P b)) (M : ℝ),
      Probability ρ → 0 ≤ M → M ≤ (2 : ℝ)^m →
      (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*N) →
      (∀ u,(P u).rank ≤ K) →
      (∀ i e f,push ρ (fun u => A u i e) f ≤
        M*weights (PMF.uniformOfFintype (Frame (Fin p) (Fin h) (Fin N) E)) f) →
      (∀ a b,accept a b ↔ CL (keyL b) a) → (∀ a b,accept b a ↔ CR (keyR b) a) →
      (∀ a b,accept a b → Admissible (T a b)
        Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation (A a) (A b)) →
      1/(N : ℝ)^c ≤ cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2) →
      cellMass (fun ab : U × U => ρ ab.1*ρ ab.2)
        (fun ab => accept ab.1 ab.2 ∧ ¬ Injecting (T ab.1 ab.2)) ≤
        ε*cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2) := by
  have hJ : 0 < 16*Fintype.card Comp := Nat.mul_pos (by decide) Fintype.card_pos
  obtain ⟨t,h,hparam⟩ := Lax342547Proofs.PreparedInjectionScale.exists_prepared_parameters
    K Cs (16*Fintype.card Comp) ε hJ hε
  refine ⟨h,fun c => ?_⟩
  obtain ⟨N₀,hN₀⟩ := hparam c
  refine ⟨N₀,?_⟩
  intro N p m hn hp hm U I _ _ E _ ρ P A accept CL CR keyL keyR T M hρ hM hcapM hcount hP hcap hleft hright hT haccept
  obtain ⟨hbudget,htail⟩ := hN₀ N hn p m hp hm
  have hN : 1 ≤ N := by have hh := hbudget.ambient; omega
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^N := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN
  have hcapMB : 2*M ≤ (2 : ℝ)^(m+N) := by
    calc
      2*M ≤ 2*(2 : ℝ)^m := mul_le_mul_of_nonneg_left hcapM (by norm_num)
      _ = (2 : ℝ)^m*2 := mul_comm _ _
      _ ≤ (2 : ℝ)^m*(2 : ℝ)^N := mul_le_mul_of_nonneg_left htwo (by positivity)
      _ = _ := (pow_add _ _ _).symm
  exact Lax342547Proofs.PreparedInjection.actual_relative_table_injection
    ρ P A accept CL CR keyL keyR T K m t Cs M (ε/(2*(16*Fintype.card Comp : ℕ))) ε
    hρ hM (by simpa using hbudget) hcapM (by simpa using hcapMB) (by simpa using hcount)
    hP hcap hleft hright hT c hJ hε.le rfl (by simpa using haccept) (by simpa using htail)

end Lax342547Proofs.UniformTableInjection
