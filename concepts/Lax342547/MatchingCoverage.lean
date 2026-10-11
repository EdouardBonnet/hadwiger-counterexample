import Lax342547.MatchingSamples
import Lax342547.DisjointSampling

/-!
---
title: Count matching occurrences covered by terminal exceptions
type: lemma
---
Disjoint matching endpoints inject edges meeting the vertex exception into exceptional positions. Every remaining edge gives an ordered pair exception; the absence of k disjoint pair exceptions bounds the actual connected matching number.
-/

namespace Lax342547.MatchingCoverage

open Lax342547.ConnectedMatching Lax342547.SampledGraph Lax342547.MatchingSamples

noncomputable def meets {Ω : Type} {m : ℕ} (sample : Fin m → Ω) (S : Ω → Prop)
    (e : Finset (Fin m)) : Prop := ∃ v ∈ e, S (sample v)

axiom matching_meets_bound {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (S : Ω → Prop) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) : by
      classical
      exact (M.filter (meets sample S)).card ≤ (Finset.univ.filter (fun v => S (sample v))).card

axiom matching_pair_embedding {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (E : Ω → Ω → Prop) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M)
    (hE : ∀ e : M, E (unitType sample e.val (hM.1 _ e.property).1).1
      (unitType sample e.val (hM.1 _ e.property).1).2) (k : ℕ) (hk : k ≤ M.card) :
    ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E (sample (a (j,false))) (sample (a (j,true)))

axiom matching_exception_bound {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (S : Ω → Prop) (E : Ω → Ω → Prop) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) (k : ℕ)
    (hcover : ∀ e : M,
      S (unitType sample e.val (hM.1 _ e.property).1).1 ∨
      S (unitType sample e.val (hM.1 _ e.property).1).2 ∨
      E (unitType sample e.val (hM.1 _ e.property).1).1 (unitType sample e.val (hM.1 _ e.property).1).2)
    (hS : by classical exact (Finset.univ.filter (fun v => S (sample v))).card < k)
    (hE : ¬ ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) :
    M.card ≤ 2*(k-1)

axiom connected_matching_exception_bound {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) {m : ℕ}
    (sample : Fin m → Ω) (k : ℕ)
    (hgood : ∀ M : Finset (Finset (Fin m)), IsTouchingMatching (sampleGraph hole hsymm sample) M →
      M.card ≤ 2*(k-1)) (hscale : 200*(k-1) < m) :
    100*connectedMatchingNumber (sampleGraph hole hsymm sample) < m

end Lax342547.MatchingCoverage
