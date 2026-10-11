import Lax342547.EntropyContainers
import Lax342547.ContainerLaws
import Lax342547.ContainerRun
import Lax342547.EntropySelectors
import Lax342547.FingerprintCounts

namespace Lax342547Proofs.EntropyContainers
open Lax342547.EntropyContainers

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.ContainerLaws Lax342547.ContainerRun
open scoped BigOperators

/--
---
conclusion: Lax342547.EntropyContainers.entropy_increment_positive
---
-/
theorem entropy_increment_positive (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : 0 < -Real.log (1-ε) := by
  have hlog := Real.log_neg (by linarith : 0 < 1-ε) (by linarith : 1-ε < 1)
  linarith

/--
---
conclusion: Lax342547.EntropyContainers.entropy_fingerprint_length
---
-/
theorem entropy_fingerprint_length {U : Type} [Fintype U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε B : ℝ)
    (law : Finset U → U → ℝ) (pick : Finset U → U) (I R : Finset U) (fuel L : ℕ)
    (hprob : ∀ ρ ∈ P, Probability ρ) (hc : Convex ℝ P)
    (hb : ∀ ρ ∈ P, 0 ≤ entropy ρ q ∧ entropy ρ q ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hspec : ∀ T, (residual P T).Nonempty →
      law T ∈ residual P T ∧ (∀ σ ∈ residual P T, entropy (law T) q ≤ entropy σ q) ∧
      pick T ∈ T ∧ ε ≤ neighborMass (law T) H (pick T) ∧ (∃ w ∈ T, H (pick T) w))
    (hL : B/(-Real.log (1-ε))+1 ≤ L) (hactive : (residual P R).Nonempty) :
    (run (fun T => (residual P T).Nonempty) pick H I fuel R).2.length ≤ L := by
  classical
  let active := fun T => (residual P T).Nonempty
  let E := fun T => entropy (law T) q
  let δ := -Real.log (1-ε)
  have hδ : 0 < δ := Lax342547.EntropyContainers.entropy_increment_positive ε hε hε1
  have hbudget : ∀ T, active T → E T ≤ B := fun T ht => (hb _ (hspec T ht).1.1).2
  have hstep : ∀ T, active T → active (next H I T (pick T)) →
      E T+(if pick T ∈ I then δ else 0) ≤ E (next H I T (pick T)) := by
    intro T ht hn
    have hT := hspec T ht
    have hN := hspec (next H I T (pick T)) hn
    have hsub := Lax342547.ContainerRun.next_subset H I T (pick T)
    have hres := Lax342547.ContainerLaws.residual_mono P T _ hsub hN.1
    by_cases hi : pick T ∈ I
    · have hzero : ∀ x, H (pick T) x → law (next H I T (pick T)) x = 0 := by
        intro x hx
        apply hN.1.2 x
        simp [next,hi,hx]
      have hh := Lax342547.ContainerLaws.recording_entropy_increment
        P q (law T) (law (next H I T (pick T))) T H (pick T) ε hprob hc
        hT.1 hT.2.1 ⟨hres,hzero⟩ hε1 hT.2.2.2.1
      simp only [hi,ite_true]
      dsimp [E,δ] at *
      linarith
    · simp only [hi,ite_false,add_zero]
      exact hT.2.1 _ hres
  have hh := Lax342547.ContainerRun.run_entropy_budget active pick H I R fuel E B δ
    hδ.le hbudget hstep hactive
  have hE : 0 ≤ E R := (hb _ (hspec R hactive).1.1).1
  have hlen : ((run active pick H I fuel R).2.length : ℝ) ≤ B/δ+1 := by
    have hs : (((run active pick H I fuel R).2.length : ℝ)-1)*δ ≤ B := by linarith
    have hh' := (le_div_iff₀ hδ).mpr hs
    linarith
  exact_mod_cast hlen.trans hL

/--
---
conclusion: Lax342547.EntropyContainers.entropy_container_family
---
-/
theorem entropy_container_family {U : Type} [Fintype U] [Nonempty U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε B : ℝ) (L : ℕ)
    (hcompact : IsCompact P) (hconvex : Convex ℝ P) (hprob : ∀ ρ ∈ P, Probability ρ)
    (hbudget : ∀ ρ ∈ P, 0 ≤ entropy ρ q ∧ entropy ρ q ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hL : B/(-Real.log (1-ε))+1 ≤ L)
    (hsuper : ∀ ρ ∈ P, ε ≤ conflictMass ρ H) :
    ∃ C : Finset (Finset U),
      C.card ≤ (Fintype.card U+1)^L ∧
      (∀ R ∈ C, ¬ (residual P R).Nonempty) ∧
      (∀ I : Finset U, (∀ x ∈ I, ∀ y ∈ I, ¬ H x y) → ∃ R ∈ C, I ⊆ R) := by
  classical
  obtain ⟨law,pick,hspec⟩ := Lax342547.EntropySelectors.entropy_selectors
    P q H ε hcompact hprob hε hsuper
  let active := fun T => (residual P T).Nonempty
  let fuel := Fintype.card U+1
  let inputs := Finset.univ.filter (fun I : Finset U => ∀ x ∈ I, ∀ y ∈ I, ¬ H x y)
  let fingerprints := inputs.image (fun I => (run active pick H I fuel Finset.univ).2)
  let C := fingerprints.image (replay active pick H fuel Finset.univ)
  have hlen : ∀ l ∈ fingerprints, l.length ≤ L := by
    intro l hl
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hl
    by_cases ha : active Finset.univ
    · exact Lax342547.EntropyContainers.entropy_fingerprint_length P q H ε B law pick I Finset.univ fuel L
        hprob hconvex hbudget hε hε1 hspec hL ha
    · have hh : (run active pick H I fuel Finset.univ).2 = [] := by
        dsimp [fuel]
        simp [run,ha]
      rw [hh]
      exact Nat.zero_le L
  refine ⟨C,?_,?_,?_⟩
  · exact (Finset.card_image_le).trans
      (Lax342547.FingerprintCounts.bounded_list_count fingerprints L hlen)
  · intro R hR
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hl
    rw [Lax342547.ContainerRun.run_replay]
    apply Lax342547.ContainerRun.run_terminal active pick H I Finset.univ fuel
    · intro T ht
      exact ⟨(hspec T ht).2.2.1,(hspec T ht).2.2.2.2⟩
    · simp [fuel]
  · intro I hi
    have hI : I ∈ inputs := Finset.mem_filter.mpr ⟨Finset.mem_univ I,hi⟩
    refine ⟨(run active pick H I fuel Finset.univ).1,?_,?_⟩
    · have hl : (run active pick H I fuel Finset.univ).2 ∈ fingerprints := Finset.mem_image.mpr ⟨I,hI,rfl⟩
      have hh := Finset.mem_image.mpr ⟨_,hl,Lax342547.ContainerRun.run_replay active pick H I Finset.univ fuel⟩
      exact hh
    · exact (Lax342547.ContainerRun.run_preserves active pick H I Finset.univ fuel
        (Finset.subset_univ I) hi).1

end Lax342547Proofs.EntropyContainers
