import Lax342547.RawFrames

/-!
---
title: Nonempty raw frame spaces
type: lemma
---
The doubled coordinate space has dimension $2(d+h)$. The plus frame is
the coordinate inclusion into its first half; the minus frame has the
prescribed Gram block in the first half and an identity in the second.
This verifies the raw frame nonemptiness construction in §2.4.
-/

namespace Lax342547.FrameExistence

open Lax342547.MomentSpace Lax342547.RawFrames

axiom frame_nonempty {B H : Type} [Fintype B] [Fintype H] (E : Matrix B B Binary) :
    Nonempty (Frame B H ((B ⊕ H) ⊕ (B ⊕ H)) E)

axiom frame_nonempty_of_card_le {B H : Type} [Fintype B] [Fintype H] {N : Type} [Fintype N]
    (E : Matrix B B Binary) (hN : 2 * (Fintype.card B + Fintype.card H) ≤ Fintype.card N) :
    Nonempty (Frame B H N E)

end Lax342547.FrameExistence
