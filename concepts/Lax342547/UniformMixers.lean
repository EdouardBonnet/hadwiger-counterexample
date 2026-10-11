import Lax342547.UnaryMixers
import Lax342547.BinaryMixers

/-!
---
title: Uniform mixing forms chosen simultaneously before any unit law
type: lemma
---
Lemma 5.5: one choice of all indexed L,R matrices and all sharp M matrices
has the unary polar-rank and bounded-row-space properties and every binary
parity rank bound. An explicit threshold in n pays for both finite unions.
The paper's displayed mixer parameters satisfy the required margin.
-/

namespace Lax342547.UniformMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw

noncomputable def threshold (k b degree J K s₀ : ℕ) : ℕ :=
  max 50 (UnaryMixers.threshold k b degree J K s₀ +
    2 ^ (2 * b + 2 * Fintype.card (Index (Component (Tag k)) J)) + 2 ^ (2 * b + 2))

def paperS₀ (k b degree K : ℕ) : ℕ :=
  40 * (K + 1) * (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 5)

def paperJ (k b degree K : ℕ) : ℕ := 101 * (paperS₀ k b degree K + K ^ 2 + 1)

axiom exists_uniform_mixers (k b degree J K s₀ : ℕ) (hk : 0 < k) (hd : 1 ≤ degree)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀)
    (n : ℕ) (hn : threshold k b degree J K s₀ ≤ n)
    (r₀ : ℕ) (hr : 2 * r₀ ≤ n) (D : Testers (k := k) (b := b) (degree := degree) hr) :
    ∃ L : Index (Component (Tag k)) J → Moment k n b degree,
      ∃ M : Fin b → Matrix (Fin n) (Fin n) Binary,
        UnaryMixers.UniformUnary D K s₀ L ∧ BinaryMixers.UniformBinary hr hd L M

axiom paper_parameters (k b degree K : ℕ) :
    (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ paperS₀ k b degree K ∧
      100 * (paperS₀ k b degree K + K ^ 2 + 1) < paperJ k b degree K

axiom exists_paper_mixers (k b degree K : ℕ) (hk : 0 < k) (hd : 1 ≤ degree) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ r₀ (hr : 2 * r₀ ≤ n)
      (D : Testers (k := k) (b := b) (degree := degree) hr),
      ∃ L : Index (Component (Tag k)) (paperJ k b degree K) → Moment k n b degree,
        ∃ M : Fin b → Matrix (Fin n) (Fin n) Binary,
          UnaryMixers.UniformUnary D K (paperS₀ k b degree K) L ∧ BinaryMixers.UniformBinary hr hd L M

end Lax342547.UniformMixers
