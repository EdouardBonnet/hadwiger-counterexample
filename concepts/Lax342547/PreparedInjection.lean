import Lax342547.TableInjection
import Lax342547.RawAcceptingInjection
import Lax342547.FrameTranspose
import Lax342547.InjectionUnion
import Lax342547.InjectionThresholds

/-!
---
title: Prepared-unit injection on actual accepting pairs
type: definition and theorem
---
Adaptive nominal pins and the actual admissible small tables retain
accepting mass under all sixteen component tests. Exponential errors are
paid relative to inverse-polynomial pair mass before any conditioning.
-/

namespace Lax342547.PreparedInjection

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableInjection
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators

abbrev Test (Comp : Type) := Comp × (Fin 2 × Fin 2) × (Bool × Bool)

def testFailure {Comp B H N U : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (P : U → Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : U → Fin 2 → Comp → Frame B H N E) (j : Test Comp) (a b : U) : Prop :=
  Failed (P a) (P b) (A a) (A b) j.1 j.2.1.1 j.2.1.2 j.2.2.1 j.2.2.2

structure Budget (K m t Cs p h N : ℕ) (η : ℝ) : Prop where
  gap : 1/(2 : ℝ)^t ≤ η/2
  ambient : p+h+1 ≤ N
  primal : p ≤ N/8
  density : m+h+1 ≤ N/10
  channel : 2*K+t+20*(K+1)*(Cs+3) ≤ h
  probes : 20*(K+1) ≤ N
  constant : m+h*K ≤ N
  small : 1/(2 : ℝ)^(N/2) ≤ η/2

variable {Comp B H N U I : Type} [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
  [Fintype U] [Fintype I] [DecidableEq B] [DecidableEq H] [DecidableEq N]
  {E : Matrix B B Binary} [Nonempty (Frame B H N E)]

axiom actual_accepting_table_loss (ρ : U → ℝ)
    (P : U → Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : U → Fin 2 → Comp → Frame B H N E)
    (accept : U → U → Prop) (CL CR : I → U → Prop) (keyL keyR : U → I)
    (T : ∀ a b,Table (P a) (P b)) (K m t Cs : ℕ) (M η : ℝ)
    (hρ : Probability ρ) (hM : 0 ≤ M)
    (hbudget : Budget K m t Cs (Fintype.card B) (Fintype.card H) (Fintype.card N) η)
    (hcapM : M ≤ (2 : ℝ)^m) (hcapMB : 2*M ≤ (2 : ℝ)^(m+Fintype.card N))
    (hcount : (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*Fintype.card N))
    (hP : ∀ u,(P u).rank ≤ K)
    (hcap : ∀ i e f,push ρ (fun u => A u i e) f ≤
      M*weights (PMF.uniformOfFintype (Frame B H N E)) f)
    (hleft : ∀ a b,accept a b ↔ CL (keyL b) a)
    (hright : ∀ a b,accept b a ↔ CR (keyR b) a)
    (hT : ∀ a b,accept a b → Admissible (T a b)
      Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation (A a) (A b)) :
    cellMass (fun ab : U × U => ρ ab.1*ρ ab.2)
      (fun ab => accept ab.1 ab.2 ∧ ¬ Injecting (T ab.1 ab.2)) ≤
      (16*Fintype.card Comp : ℕ)*(η*cellMass (fun ab : U × U => ρ ab.1*ρ ab.2)
        (fun ab => accept ab.1 ab.2)+
        (1/(2 : ℝ)^(Fintype.card N/100)+1/(2 : ℝ)^Fintype.card N))

axiom actual_relative_table_injection (ρ : U → ℝ)
    (P : U → Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : U → Fin 2 → Comp → Frame B H N E)
    (accept : U → U → Prop) (CL CR : I → U → Prop) (keyL keyR : U → I)
    (T : ∀ a b,Table (P a) (P b)) (K m t Cs : ℕ) (M η ε : ℝ)
    (hρ : Probability ρ) (hM : 0 ≤ M)
    (hbudget : Budget K m t Cs (Fintype.card B) (Fintype.card H) (Fintype.card N) η)
    (hcapM : M ≤ (2 : ℝ)^m) (hcapMB : 2*M ≤ (2 : ℝ)^(m+Fintype.card N))
    (hcount : (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*Fintype.card N))
    (hP : ∀ u,(P u).rank ≤ K)
    (hcap : ∀ i e f,push ρ (fun u => A u i e) f ≤
      M*weights (PMF.uniformOfFintype (Frame B H N E)) f)
    (hleft : ∀ a b,accept a b ↔ CL (keyL b) a)
    (hright : ∀ a b,accept b a ↔ CR (keyR b) a)
    (hT : ∀ a b,accept a b → Admissible (T a b)
      Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation (A a) (A b))
    (c : ℕ) (hJ : 0 < 16*Fintype.card Comp) (hε : 0 ≤ ε)
    (hη : η = ε/(2*(16*Fintype.card Comp : ℕ)))
    (haccept : 1/(Fintype.card N : ℝ)^c ≤ cellMass (fun ab : U × U => ρ ab.1*ρ ab.2)
      (fun ab => accept ab.1 ab.2))
    (htail : (16*Fintype.card Comp : ℕ)*(1/(2 : ℝ)^(Fintype.card N/100)+1/(2 : ℝ)^Fintype.card N) ≤
      (ε/2)/(Fintype.card N : ℝ)^c) :
    cellMass (fun ab : U × U => ρ ab.1*ρ ab.2)
      (fun ab => accept ab.1 ab.2 ∧ ¬ Injecting (T ab.1 ab.2)) ≤
      ε*cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2)

end Lax342547.PreparedInjection
