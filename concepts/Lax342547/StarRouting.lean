import Lax342547.ChannelFactorization

/-!
---
title: Low-rank tester routing along tag stars
type: lemma
---
Ordered tester matrices have rank at most r. Summing cut moments along a tag star removes its even center multiplicity. Forbidden ordinary centers vanish, and each component receives at most two routed testers.
-/

namespace Lax342547.StarRouting

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.TagGeometry Lax342547.CutProfiles Lax342547.Atoms

axiom matrix_sum_rank {I B : Type} [Fintype I] [Fintype B]
    (M : I → Matrix B B Binary) :
    (∑ i, M i).rank ≤ ∑ i, (M i).rank

noncomputable def orderedTesterMatrix {k n b degree r : ℕ}
    (hr : 2 * r ≤ n) (c : Fin n → Lax342547.TagGeometry.Base k n) : Moment k n b degree := by
  classical
  exact ∑ ρ, Matrix.vecMulVec
    (Pi.single (emptySelector b degree, some (c (pairLeft hr ρ))) 1)
    (Pi.single (emptySelector b degree, some (c (pairRight hr ρ))) 1)

axiom ordered_tester_rank {k n b degree r : ℕ}
    (hr : 2 * r ≤ n) (c : Fin n → Lax342547.TagGeometry.Base k n) :
    (orderedTesterMatrix (b := b) (degree := degree) hr c).rank ≤ r

axiom tester_matrix_representation {k n b degree r : ℕ}
    (hr : 2 * r ≤ n) (c : Fin n → Lax342547.TagGeometry.Base k n) :
    matrixPair (orderedTesterMatrix (b := b) (degree := degree) hr c) = blockTester hr c

axiom interval_center_excluded {k : ℕ} (d : Tag k) : d ∉ interval k d

axiom ordinary_tester_disallowed_zero {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (d t l : Tag k) (hl : l ∉ interval k d) (w : Representation k n b degree) :
    blockTester hr (ordinary d t) (w.val l) = 0

noncomputable def incidentEquiv {k : ℕ} (l : Tag k) :
    {t : Tag k // t ≠ l} ≃ {e : Component (Tag k) // l ∈ e.val} := by
  classical
  let f : {t : Tag k // t ≠ l} → {e : Component (Tag k) // l ∈ e.val} :=
    fun t => ⟨⟨{l, t.val}, Finset.card_pair t.property.symm⟩, by simp⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v h
    apply Subtype.ext
    have hs : ({l, u.val} : Finset (Tag k)) = {l, v.val} :=
      congrArg (fun e : {e : Component (Tag k) // l ∈ e.val} => e.val.val) h
    have hu : u.val ∈ ({l, v.val} : Finset (Tag k)) := by rw [← hs]; simp
    simpa [u.property] using hu
  · intro e
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.val.property
    have hl : l = a ∨ l = b := by simpa only [he, Finset.mem_insert, Finset.mem_singleton] using e.property
    rcases hl with rfl | rfl
    · refine ⟨⟨b, hab.symm⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext he.symm
    · refine ⟨⟨a, hab⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change ({l, a} : Finset (Tag k)) = e.val.val
      rw [he, Finset.pair_comm]

axiom star_cut_sum {k : ℕ} {X : Type} [AddCommGroup X] [Module Binary X]
    (w : Tag k → X) (l : Tag k) :
    (∑ e : {e : Component (Tag k) // l ∈ e.val}, ∑ t ∈ e.val.val, w t) =
      ∑ t : {t : Tag k // t ≠ l}, w t.val

axiom incidence_sum {k : ℕ} {X : Type} [AddCommMonoid X]
    (F : Tag k → Component (Tag k) → X) :
    (∑ e, ∑ d ∈ e.val, F d e) = ∑ d, ∑ e : {e : Component (Tag k) // d ∈ e.val}, F d e.val

noncomputable def starMatrix {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (c : Tag k → Fin n → Base k n) (coeff : Tag k → Binary) (e : Component (Tag k)) :
    Moment k n b degree := ∑ d ∈ e.val, coeff d • orderedTesterMatrix hr (c d)

axiom star_matrix_representation {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (c : Tag k → Fin n → Base k n) (coeff : Tag k → Binary)
    (w : Representation k n b degree) :
    (∑ e, matrixPair (starMatrix (b := b) (degree := degree) hr c coeff e)
      ((representationCut k n b degree w) e)) =
    ∑ d, coeff d * ∑ l : {l : Tag k // l ≠ d}, blockTester hr (c d) (w.val l.val)

axiom matrix_smul_rank {B : Type} [Fintype B] (M : Matrix B B Binary) (a : Binary) :
    (a • M).rank ≤ M.rank

axiom matrix_add_rank {B : Type} [Fintype B] (M Q : Matrix B B Binary) :
    (M + Q).rank ≤ M.rank + Q.rank

axiom matrix_finset_sum_rank {I B : Type} [Fintype B] (s : Finset I)
    (M : I → Matrix B B Binary) (R : ℕ) (hM : ∀ i ∈ s, (M i).rank ≤ R) :
    (∑ i ∈ s, M i).rank ≤ s.card * R

axiom star_matrix_rank {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (c : Tag k → Fin n → Base k n) (coeff : Tag k → Binary) (e : Component (Tag k)) :
    (starMatrix (b := b) (degree := degree) hr c coeff e).rank ≤ 2 * r

end Lax342547.StarRouting
