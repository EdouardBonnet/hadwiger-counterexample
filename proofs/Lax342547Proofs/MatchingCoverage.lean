import Lax342547.MatchingCoverage
import Lax342547.MatchingSamples
import Lax342547Proofs.HadwigerMatching.BasicMatching

namespace Lax342547Proofs.MatchingCoverage
open Lax342547.MatchingCoverage

set_option backward.isDefEq.respectTransparency false
open Lax342547.ConnectedMatching Lax342547.SampledGraph Lax342547.MatchingSamples

/--
---
conclusion: Lax342547.MatchingCoverage.matching_meets_bound
---
-/
theorem matching_meets_bound {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (S : Ω → Prop) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) : by
      classical
      exact (M.filter (meets sample S)).card ≤ (Finset.univ.filter (fun v => S (sample v))).card := by
  classical
  let A := M.filter (meets sample S)
  let P := Finset.univ.filter (fun v => S (sample v))
  have hex : ∀ e : A, ∃ v : P, v.val ∈ e.val := by
    intro e
    obtain ⟨v,hv,hS⟩ := (Finset.mem_filter.mp e.property).2
    exact ⟨⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ v,hS⟩⟩,hv⟩
  choose hit hhit using hex
  have hinj : Function.Injective hit := by
    intro e f heq
    apply Subtype.ext
    by_contra hef
    have heM := (Finset.mem_filter.mp e.property).1
    have hfM := (Finset.mem_filter.mp f.property).1
    have hd := hM.2.1 _ heM _ hfM hef
    exact Finset.disjoint_left.mp hd (hhit e) (heq.symm ▸ hhit f)
  have hc := Fintype.card_le_of_injective hit hinj
  simpa only [Fintype.card_coe] using hc

/--
---
conclusion: Lax342547.MatchingCoverage.matching_pair_embedding
---
-/
theorem matching_pair_embedding {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (E : Ω → Ω → Prop) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M)
    (hE : ∀ e : M, E (unitType sample e.val (hM.1 _ e.property).1).1
      (unitType sample e.val (hM.1 _ e.property).1).2) (k : ℕ) (hk : k ≤ M.card) :
    ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E (sample (a (j,false))) (sample (a (j,true))) := by
  classical
  let edge : Fin k ↪ M := (Fin.castLEEmb hk).trans M.equivFin.symm.toEmbedding
  let orient : M × Bool ↪ Fin m := ⟨_,Lax342547.MatchingSamples.matching_orientation_injective _ M hM⟩
  let a : Fin k × Bool ↪ Fin m := (Function.Embedding.prodMap edge (Function.Embedding.refl Bool)).trans orient
  refine ⟨a,?_⟩
  intro j
  exact hE (edge j)

/--
---
conclusion: Lax342547.MatchingCoverage.matching_exception_bound
---
-/
theorem matching_exception_bound {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (S : Ω → Prop) (E : Ω → Ω → Prop) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) (k : ℕ)
    (hcover : ∀ e : M,
      S (unitType sample e.val (hM.1 _ e.property).1).1 ∨
      S (unitType sample e.val (hM.1 _ e.property).1).2 ∨
      E (unitType sample e.val (hM.1 _ e.property).1).1 (unitType sample e.val (hM.1 _ e.property).1).2)
    (hS : by classical exact (Finset.univ.filter (fun v => S (sample v))).card < k)
    (hE : ¬ ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) :
    M.card ≤ 2*(k-1) := by
  classical
  let A := M.filter (meets sample S)
  let B := M.filter (fun e => ¬ meets sample S e)
  have hA : A.card < k := (Lax342547.MatchingCoverage.matching_meets_bound hole hsymm sample S M hM).trans_lt hS
  have hB : B.card < k := by
    by_contra hn
    have hk : k ≤ B.card := Nat.le_of_not_gt hn
    have hBM : IsTouchingMatching (sampleGraph hole hsymm sample) B := by
      refine ⟨?_,?_,?_⟩
      · intro e he
        exact hM.1 e (Finset.mem_filter.mp he).1
      · intro e he f hf hne
        exact hM.2.1 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hne
      · intro e he f hf hne
        exact hM.2.2 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hne
    apply hE
    apply Lax342547.MatchingCoverage.matching_pair_embedding hole hsymm sample E B hBM _ k hk
    intro e
    let em : M := ⟨e.val,(Finset.mem_filter.mp e.property).1⟩
    have hc := hcover em
    have hnS := (Finset.mem_filter.mp e.property).2
    rcases hc with h₁|h₂|h₃
    · exact (hnS ⟨oriented e.val _ false,Lax342547.MatchingSamples.oriented_mem e.val _ false,h₁⟩).elim
    · exact (hnS ⟨oriented e.val _ true,Lax342547.MatchingSamples.oriented_mem e.val _ true,h₂⟩).elim
    · exact h₃
  have hsum : A.card+B.card = M.card := Finset.card_filter_add_card_filter_not _
  omega

/--
---
conclusion: Lax342547.MatchingCoverage.connected_matching_exception_bound
---
-/
theorem connected_matching_exception_bound {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (k : ℕ)
    (hgood : ∀ M : Finset (Finset (Fin m)), IsTouchingMatching (sampleGraph hole hsymm sample) M →
      M.card ≤ 2*(k-1)) (hscale : 200*(k-1) < m) :
    100*connectedMatchingNumber (sampleGraph hole hsymm sample) < m := by
  obtain ⟨M,hM,hcard⟩ := Lax342547Proofs.HadwigerMatching.exists_matching_card_eq_number
    (sampleGraph hole hsymm sample)
  have hh := hgood M hM
  rw [hcard] at hh
  omega

end Lax342547Proofs.MatchingCoverage
