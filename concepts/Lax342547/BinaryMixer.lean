import Lax342547.Atoms
import Lax342547.OrderedMixerLaw
import Lax342547.SharpMixerLaw

/-!
---
title: Bilinear parts of ordered evaluations on every atom flavor
type: lemma
---
The mixed coefficient matrix is defined directly by evaluating the two
point inputs. Its free and sharp submatrices are the corresponding
ambient matrix restrictions, independently of the tags and flavors.
Thus the rank estimates on the always retained blocks imply the required
rank bounds on each full flavor parameter space.
-/

namespace Lax342547.BinaryMixer

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.Atoms Lax342547.AtomDirections

abbrev ParameterIndex {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  {i : Base k n // i ∈ retained l f}

noncomputable def directions {k n b degree : ℕ} (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k) : Matrix (Coordinate k n b degree) (ParameterIndex n l f) Binary := by
  classical
  exact fun i j => if i.2 = some j.val then selectorEval s i.1 else 0

noncomputable def pointInput {k n b degree : ℕ} (s : Fin b → Binary)
    {l : Tag k} {f : Flavor k} (p : Parameters n l f) : Vector k n b degree :=
  point selectorEval s (parameterValue p)

noncomputable def mixedMatrix {P Q : Type} [DecidableEq P] [DecidableEq Q]
    (f : (P → Binary) → (Q → Binary) → Binary) : Matrix P Q Binary :=
  fun i j => f (Pi.single i 1) (Pi.single j 1) + f (Pi.single i 1) 0 +
    f 0 (Pi.single j 1) + f 0 0

noncomputable def bilinearPart {k n b degree : ℕ} (A : Moment k n b degree)
    (s t : Fin b → Binary) (l m : Tag k) (f g : Flavor k) :
    Matrix (ParameterIndex n l f) (ParameterIndex n m g) Binary := by
  classical
  exact mixedMatrix (fun p q => A.toBilin' (pointInput s p) (pointInput t q))

def ambientParity {I F : Type} [Fintype F] (L : F → Matrix I I Binary)
    (a b : F → Binary) (E : Matrix I I Binary) (c d : Binary) : Matrix I I Binary :=
  (∑ j, (a j • L j + b j • (L j).transpose)) + c • E + d • E.transpose

axiom ambientParity_eval {I F : Type} [Fintype I] [DecidableEq I] [Fintype F]
    (L : F → Matrix I I Binary) (a b : F → Binary) (E : Matrix I I Binary) (c d : Binary)
    (x y : I → Binary) :
    (ambientParity L a b E c d).toBilin' x y =
      (∑ j, (a j * (L j).toBilin' x y + b j * (L j).toBilin' y x)) +
        c * E.toBilin' x y + d * E.toBilin' y x

axiom pointInput_affine {k n b degree : ℕ} (s : Fin b → Binary)
    {l : Tag k} {f : Flavor k} (p : Parameters n l f) :
    pointInput (degree := degree) s p = pointInput s (0 : Parameters n l f) +
      (directions s l f).mulVec p

axiom bilinearPart_eq {k n b degree : ℕ} (A : Moment k n b degree)
    (s t : Fin b → Binary) (l m : Tag k) (f g : Flavor k) :
    bilinearPart A s t l m f g = (directions s l f).transpose * A * directions t m g

axiom block_rank_le {k n b degree : ℕ} (A : Moment k n b degree)
    (s t : Fin b → Binary) (l m : Tag k) (f g : Flavor k)
    (c : Fin n → Base k n)
    (hc : ∀ i, c i ∈ retained l f) (hd : ∀ i, c i ∈ retained m g) :
    ((blockDirections s c).transpose * A * blockDirections t c).rank ≤
      (bilinearPart A s t l m f g).rank

axiom parity_free_block {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (a b' : F → Binary)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (c d : Binary) (s t : Fin b → Binary) :
    (blockDirections s free).transpose * ambientParity L a b' (selfGram hr hd M) c d *
      blockDirections t free =
        OrderedMixerLaw.familyParity (blockDirections s free) (blockDirections t free) a b' L

axiom selfGram_parity_sharp_block {k n b degree r : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (c d : Binary) (s t : Fin b → Binary) :
    (blockDirections (k := k) s sharp).transpose *
      (c • selfGram hr hd M + d • (selfGram hr hd M).transpose) * blockDirections t sharp =
      c • SharpMixerLaw.weighted (fun a => s a + t a) M +
        d • (SharpMixerLaw.weighted (fun a => s a + t a) M).transpose

end Lax342547.BinaryMixer
