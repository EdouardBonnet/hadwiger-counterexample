import Lax342547.PreparedInjection
import Lax342547Proofs.TableInjection
import Lax342547Proofs.RawAcceptingInjection
import Lax342547Proofs.FrameTranspose
import Lax342547Proofs.InjectionUnion
import Lax342547Proofs.InjectionThresholds

namespace Lax342547Proofs.PreparedInjection

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableInjection
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.RetainedImages
open Lax342547.RelativeEntropy Lax342547.PreparedInjection Lax342547.FrameTranspose
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem test_count {Comp : Type} [Fintype Comp] : Fintype.card (Test Comp) = 16*Fintype.card Comp := by
  simp [Test,Fintype.card_prod]
  omega

variable {Comp B H N U I : Type} [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
  [Fintype U] [Fintype I] [DecidableEq B] [DecidableEq H] [DecidableEq N]
  {E : Matrix B B Binary} [Nonempty (Frame B H N E)]

theorem primalImage_budget (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2) (s : Bool) :
    Module.finrank Binary (primalImage P A e i s) ≤ P.rank := by
  have hp : pinnedPrimal P i (e,s) ≤ Lax342547.ProjectedPins.projected P i (e,s) := by
    intro v hv
    refine ⟨primalEmbedding i v,hv,?_⟩
    simp [Lax342547.ProjectedPins.primalProjection,primalEmbedding]
  exact (Submodule.finrank_map_le _ _).trans ((Submodule.finrank_mono hp).trans
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (e,s))).trans
      (Lax342547Proofs.ProjectedPins.projected_rank P i)))

theorem protected_budget (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (e : Comp) (i : Fin 2) (s : Bool) :
    Module.finrank Binary (protectedChannel P i (e,s)) ≤ P.rank :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (e,s))).trans
    (Lax342547Proofs.TableSpaces.protected_rank P i)

theorem signed_accepting_injection (ρ : U → ℝ)
    (P : U → Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : U → Fin 2 → Comp → Frame B H N E) (C : I → U → Prop) (key : U → I)
    (e : Comp) (i z : Fin 2) (s : Bool) (K m t Cs : ℕ) (M η : ℝ)
    (hρ : Probability ρ) (hM : 0 ≤ M)
    (hbudget : Budget K m t Cs (Fintype.card B) (Fintype.card H) (Fintype.card N) η)
    (hcapM : M ≤ (2 : ℝ)^m) (hcapMB : 2*M ≤ (2 : ℝ)^(m+Fintype.card N))
    (hcount : (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*Fintype.card N))
    (hP : ∀ u,(P u).rank ≤ K)
    (hcap : ∀ i e f,push ρ (fun u => A u i e) f ≤
      M*weights (PMF.uniformOfFintype (Frame B H N E)) f) :
    (∑ b,ρ b*cellMass ρ (fun a => C (key b) a ∧
      Lax342547.FiniteInjection.pinFailure (primalImage (P a) (A a) e i s)
        (oppositeChannel (A b) e z s) (protectedChannel (P b) z (e,s)))) ≤
      η*(∑ b,ρ b*cellMass ρ (C (key b))) +
        1/(2 : ℝ)^(Fintype.card N/100)+1/(2 : ℝ)^Fintype.card N := by
  have hη : 0 ≤ η := by
    have hp : (0 : ℝ) < 1/(2 : ℝ)^t := by positivity
    linarith [hbudget.gap]
  have hV (a : U) : Module.finrank Binary (primalImage (P a) (A a) e i s) ≤ K :=
    (primalImage_budget (P a) (A a) e i s).trans (hP a)
  have hS (b : U) : Module.finrank Binary (protectedChannel (P b) z (e,s)) ≤ K :=
    (protected_budget (P b) e z s).trans (hP b)
  have hrange (a : U) : primalImage (P a) (A a) e i s ≤
      LinearMap.range (primalMatrix (A a) e i s).mulVecLin := by
    rintro v ⟨w,_,hw⟩
    exact ⟨w,hw⟩
  cases s
  · letI : Nonempty (Frame B H N E.transpose) := ⟨transposeFrame (Classical.choice inferInstance)⟩
    exact Lax342547Proofs.RawAcceptingInjection.exponential_accepting_injection E.transpose ρ ρ C key
      (fun a => transposeFrame (A a i e)) (fun b => transposeFrame (A b z e))
      (fun a => primalImage (P a) (A a) e i false) (fun b => protectedChannel (P b) z (e,false))
      K m t Cs M M η hρ hρ hM hM hη hbudget.gap hbudget.ambient hbudget.primal
      hbudget.density hcapM hcapMB hcount hbudget.channel hbudget.probes hbudget.constant hbudget.small
      hrange hV hS
      (Lax342547Proofs.FrameTranspose.capped_transpose_frame E ρ (fun a => A a i e) M (hcap i e))
      (Lax342547Proofs.FrameTranspose.capped_transpose_frame E ρ (fun b => A b z e) M (hcap z e))
  · exact Lax342547Proofs.RawAcceptingInjection.exponential_accepting_injection E ρ ρ C key
      (fun a => A a i e) (fun b => A b z e)
      (fun a => primalImage (P a) (A a) e i true) (fun b => protectedChannel (P b) z (e,true))
      K m t Cs M M η hρ hρ hM hM hη hbudget.gap hbudget.ambient hbudget.primal
      hbudget.density hcapM hcapMB hcount hbudget.channel hbudget.probes hbudget.constant hbudget.small
      hrange hV hS (hcap i e) (hcap z e)

theorem pair_swap (ρ : U → ℝ) (F : U → U → Prop) :
    cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => F ab.1 ab.2) =
      cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => F ab.2 ab.1) := by
  classical
  unfold cellMass
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.sum_comm]
  congr 1
  funext a
  congr 1
  funext b
  simp only
  split_ifs <;> ring

omit [DecidableEq B] [DecidableEq H] [DecidableEq N]

/--
---
conclusion: Lax342547.PreparedInjection.actual_accepting_table_loss
---
All roles and signs are tested under the original independent unit law;
admissibility supplies the numerical flag identification only on accepted pairs.
-/
theorem actual_accepting_table_loss (ρ : U → ℝ)
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
        (1/(2 : ℝ)^(Fintype.card N/100)+1/(2 : ℝ)^Fintype.card N)) := by
  classical
  classical
  have hlawL (b : U) : CL (keyL b) = (fun a => accept a b) :=
    funext (fun a => propext (hleft a b).symm)
  have hlawR (b : U) : CR (keyR b) = (fun a => accept b a) :=
    funext (fun a => propext (hright a b).symm)
  have htests (j : Test Comp) :
      (∑ b,ρ b*cellMass ρ (fun a => accept a b ∧ testFailure P A j a b)) ≤
        η*(∑ b,ρ b*cellMass ρ (fun a => accept a b))+
        (1/(2 : ℝ)^(Fintype.card N/100)+1/(2 : ℝ)^Fintype.card N) := by
    obtain ⟨e,⟨i,z⟩,s,role⟩ := j
    cases role
    · have hh := signed_accepting_injection ρ P A CL keyL e i z s K m t Cs M η
        hρ hM hbudget hcapM hcapMB hcount hP hcap
      simp_rw [hlawL] at hh
      simpa [testFailure,Failed,add_assoc] using hh
    · have hh := signed_accepting_injection ρ P A CR keyR e i z s K m t Cs M η
        hρ hM hbudget hcapM hcapMB hcount hP hcap
      simp_rw [hlawR] at hh
      rw [← Lax342547Proofs.InjectionUnion.pair_event_mass,
        ← Lax342547Proofs.InjectionUnion.pair_event_mass] at hh
      rw [pair_swap ρ (fun a b => accept b a ∧ Lax342547.FiniteInjection.pinFailure
        (primalImage (P a) (A a) e i s) (oppositeChannel (A b) e z s) (protectedChannel (P b) z (e,s))),
        pair_swap ρ (fun a b => accept b a)] at hh
      rw [Lax342547Proofs.InjectionUnion.pair_event_mass ρ ρ
        (fun a b => accept a b ∧ Lax342547.FiniteInjection.pinFailure
          (primalImage (P b) (A b) e i s) (oppositeChannel (A a) e z s) (protectedChannel (P a) z (e,s))),
        Lax342547Proofs.InjectionUnion.pair_event_mass ρ ρ accept] at hh
      simpa [testFailure,Failed,add_assoc] using hh
  have hu := Lax342547Proofs.InjectionUnion.finite_injection_union ρ ρ accept (testFailure P A)
    η (1/(2 : ℝ)^(Fintype.card N/100)+1/(2 : ℝ)^Fintype.card N) hρ.1 hρ.1 htests
  rw [test_count] at hu
  apply le_trans _ hu
  apply Lax342547Proofs.FiniteSampling.cell_mass_mono (fun ab : U × U => ρ ab.1*ρ ab.2) _ _
    (fun ab => mul_nonneg (hρ.1 ab.1) (hρ.1 ab.2))
  rintro ⟨a,b⟩ ⟨hab,hbad⟩
  refine ⟨hab,?_⟩
  have hi : ¬ Injecting (rawTable (P a) (P b) (A a) (A b)) := fun hh =>
    hbad ((Lax342547Proofs.TableInjection.admissible_injection_iff _ _ _ _ _ (hT a b hab)).mpr hh)
  rw [Lax342547Proofs.TableInjection.actual_table_injecting_iff] at hi
  push Not at hi
  obtain ⟨e,i,z,s,role,hh⟩ := hi
  exact ⟨⟨e,⟨i,z⟩,s,role⟩,hh⟩

/--
---
conclusion: Lax342547.PreparedInjection.actual_relative_table_injection
---
-/
theorem actual_relative_table_injection (ρ : U → ℝ)
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
      ε*cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2) := by
  classical
  have ha : 0 ≤ cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2) := by
    classical
    unfold cellMass
    exact Finset.sum_nonneg (fun ab _ => by split_ifs; exact mul_nonneg (hρ.1 ab.1) (hρ.1 ab.2); exact le_rfl)
  have hh := actual_accepting_table_loss ρ P A accept CL CR keyL keyR T K m t Cs M η
    hρ hM hbudget hcapM hcapMB hcount hP hcap hleft hright hT
  rw [hη] at hh
  apply Lax342547Proofs.InjectionAsymptotics.relative_union_budget (16*Fintype.card Comp) ε _ _ _ hJ hε ha hh
  exact htail.trans (by simpa only [div_eq_mul_inv,one_div,one_mul] using
    mul_le_mul_of_nonneg_left haccept (by positivity : (0 : ℝ) ≤ ε/2))

end Lax342547Proofs.PreparedInjection
