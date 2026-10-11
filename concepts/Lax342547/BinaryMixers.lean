import Lax342547.BinaryMixer

/-!
---
title: Simultaneous binary mixer estimates for all labels and flavors
type: lemma
---
The good events quantify over every pair of distinct selector labels and
every nonzero ordered parity. Finite unions give a failure bound tending
to zero with n. The rank condition is n ≤ 5r, avoiding any rounding of
the paper's n/5 threshold.
-/

namespace Lax342547.BinaryMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.Atoms Lax342547.AtomDirections Lax342547.BinaryMixer

def MixerGood {k n b degree : ℕ} {F : Type} [Fintype F]
    (L : F → Moment k n b degree) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ a b' : F → Binary,
    (∃ j, a j ≠ 0 ∨ b' j ≠ 0) →
      n ≤ 5 * (OrderedMixerLaw.familyParity (blockDirections s free)
        (blockDirections t free) a b' L).rank

def SharpGood {n b : ℕ} (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ c d : Binary, (c ≠ 0 ∨ d ≠ 0) →
    n ≤ 5 * (c • SharpMixerLaw.weighted (fun a => s a + t a) M +
      d • (SharpMixerLaw.weighted (fun a => s a + t a) M).transpose).rank

def UniformBinary {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ l m : Tag k, ∀ f g : Flavor k,
    ∀ a b' : F → Binary, ∀ c d : Binary,
      ((∃ j, a j ≠ 0 ∨ b' j ≠ 0) ∨ c ≠ 0 ∨ d ≠ 0) →
        n ≤ 5 * (bilinearPart (ambientParity L a b' (selfGram hr hd M) c d) s t l m f g).rank

abbrev MixerTest (b : ℕ) (F : Type) :=
  (Fin b → Binary) × (Fin b → Binary) × (F → Binary) × (F → Binary)

abbrev SharpTest (b : ℕ) := (Fin b → Binary) × (Fin b → Binary) × Binary × Binary

open scoped ENNReal

noncomputable def failureBound (b m n : ℕ) : ℝ≥0∞ := 2 ^ (2 * b + 2 * m) / 2 ^ n

axiom uniform_of_restrictions {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (hL : MixerGood L) (hM : SharpGood M) : UniformBinary hr hd L M

axiom mixer_failure_bound {k n b degree : ℕ} {F : Type} [Fintype F] [DecidableEq F]
    (hd : 1 ≤ degree) (hn : 50 ≤ n) :
    (PMF.uniformOfFintype (F → Moment k n b degree)).toOuterMeasure
      {L | ¬ MixerGood L} ≤ failureBound b (Fintype.card F) n

axiom sharp_failure_bound {n b : ℕ} (hn : 50 ≤ n) :
    (PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)).toOuterMeasure
      {M | ¬ SharpGood M} ≤ failureBound b 1 n

end Lax342547.BinaryMixers
