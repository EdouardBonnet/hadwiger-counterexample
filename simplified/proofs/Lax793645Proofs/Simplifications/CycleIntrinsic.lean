import Lax793645Proofs.Simplifications.CycleTrace
import Lax793645Proofs.Simplifications.CycleMatchings
import Mathlib.Algebra.Group.Fin.Basic
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRanks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section

def traceEdges {r : ℕ} (t : Fin (2*r+1) → Bool) : Fin (2*r+1) → Bool :=
  fun l => Bool.xor (t l) (t (l+1))

theorem traceEdges_normalize {r : ℕ} (t : Fin (2*r+1) → Bool) :
    traceEdges (normalizeTrace t)=traceEdges t := by
  classical
  unfold normalizeTrace
  split_ifs
  · rfl
  · funext l
    change Bool.xor (!(t l)) (!(t (l+1)))=Bool.xor (t l) (t (l+1))
    cases t l <;> cases t (l+1) <;> rfl

theorem cycle_majority_unique {r : ℕ} {s t : Fin (2*r+1) → Bool}
    (hs : majorityZero s) (ht : majorityZero t) (he : traceEdges s=traceEdges t) : s=t := by
  apply normalized_edge_trace_unique s t hs ht
  intro i
  have hi : (i.castSucc : Fin (2*r+1))+1=i.succ := by
    apply Fin.ext
    simp only [Fin.val_add,Fin.val_castSucc,Fin.val_succ,Fin.val_one']
    have h := i.isLt
    rw [Nat.mod_eq_of_lt (by omega : 1<2*r+1),Nat.mod_eq_of_lt (by omega)]
  simpa only [traceEdges,hi] using congrFun he i.castSucc

/-- The canonical object is a bitvector, not a matrix representation. -/
def intrinsicTrace {r : ℕ} (edgeBits : Fin (2*r+1) → Bool)
    (h : ∃ t, traceEdges t=edgeBits) : Fin (2*r+1) → Bool := normalizeTrace h.choose

theorem intrinsicTrace_majority {r : ℕ} (edgeBits : Fin (2*r+1) → Bool)
    (h : ∃ t, traceEdges t=edgeBits) : majorityZero (intrinsicTrace edgeBits h) :=
  normalized_majority h.choose (by simp only [Fintype.card_fin]; exact ⟨r,rfl⟩)

theorem intrinsicTrace_edges {r : ℕ} (edgeBits : Fin (2*r+1) → Bool)
    (h : ∃ t, traceEdges t=edgeBits) : traceEdges (intrinsicTrace edgeBits h)=edgeBits :=
  (traceEdges_normalize h.choose).trans h.choose_spec

theorem intrinsicTrace_unique {r : ℕ} (edgeBits : Fin (2*r+1) → Bool)
    (h : ∃ t, traceEdges t=edgeBits) {t : Fin (2*r+1) → Bool}
    (ht : majorityZero t) (he : traceEdges t=edgeBits) : t=intrinsicTrace edgeBits h :=
  cycle_majority_unique ht (intrinsicTrace_majority edgeBits h)
    (he.trans (intrinsicTrace_edges edgeBits h).symm)

theorem intrinsicTrace_common {r : ℕ} (x y : Fin (2*r+1) → Bool)
    (hx : ∃ t, traceEdges t=x) (hy : ∃ t, traceEdges t=y) (he : x=y) :
    intrinsicTrace x hx=intrinsicTrace y hy :=
  cycle_majority_unique (intrinsicTrace_majority x hx) (intrinsicTrace_majority y hy)
    ((intrinsicTrace_edges x hx).trans (he.trans (intrinsicTrace_edges y hy).symm))

def boolBit (b : Bool) : ZMod 2 := if b then 1 else 0

def intrinsicChi {r : ℕ} (x : Fin (2*r+1) → Bool) (hx : ∃ t, traceEdges t=x) : ZMod 2 :=
  ∑ l, boolBit (intrinsicTrace x hx l)

theorem intrinsicChi_common {r : ℕ} (x y : Fin (2*r+1) → Bool)
    (hx : ∃ t, traceEdges t=x) (hy : ∃ t, traceEdges t=y) (he : x=y) :
    intrinsicChi x hx=intrinsicChi y hy := by
  unfold intrinsicChi
  rw [intrinsicTrace_common x y hx hy he]

theorem matrix_nonzero_rank {I J : Type} [Fintype I] [Fintype J] {M : Mat I J}
    (h : M ≠ 0) : 1 ≤ M.rank := by
  by_contra hg
  have he : colSp M=⊥ := Submodule.finrank_eq_zero.mp (by
    rw [show Module.finrank F (colSp M)=M.rank from rfl]; omega)
  have hm : M.mulVecLin=0 := LinearMap.range_eq_bot.mp he
  apply h
  exact coe_mv_inj (J:=J) (show M.mulVecLin=Matrix.mulVecLin 0 by rw [hm,Matrix.mulVecLin_zero])

/-- One outgoing component per ordinary bit already suffices for the support
bound; counting both incident edges is unnecessary. -/
theorem ordinary_support_from_components {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (o : V → Bool) (x : V → Mat I J) (howned : ∀ l, o l=true → x l ≠ 0) :
    (ones o).card ≤ ∑ l, (x l).rank := by
  classical
  rw [ones,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro l _
  split_ifs with h
  · exact matrix_nonzero_rank (howned l h)
  · exact Nat.zero_le _

theorem intrinsic_shared_support {r D : ℕ} {I J : Type} [Fintype I] [Fintype J]
    (edgeBits : Fin (2*r+1) → Bool) (htrace : ∃ t, traceEdges t=edgeBits)
    (o : Fin (2*r+1) → Bool) (x : Fin (2*r+1) → Mat I J)
    (howned : ∀ l, o l=true → x l ≠ 0) (hrank : (∑ l, (x l).rank) ≤ 2*D) :
    (ones (fun l => Bool.xor (intrinsicTrace edgeBits htrace l) (o l))).card ≤ r+2*D := by
  have h := shared_support_bound (intrinsicTrace edgeBits htrace) o D
    (intrinsicTrace_majority edgeBits htrace)
    ((ordinary_support_from_components o x howned).trans hrank)
  simp only [Fintype.card_fin,Nat.add_sub_cancel] at h
  omega

theorem boolBit_xor (s t : Bool) : boolBit (Bool.xor s t)=boolBit s+boolBit t := by
  cases s <;> cases t <;> simp [boolBit,CharTwo.add_self_eq_zero]

theorem intrinsic_tester_identity {r : ℕ}
    (edgeBits : Fin (2*r+1) → Bool) (htrace : ∃ t, traceEdges t=edgeBits)
    (o : Fin (2*r+1) → Bool) (shared : Fin (2*r+1) → ZMod 2)
    (hs : ∀ l, shared l=boolBit (edgeBits l)+boolBit (o l)+boolBit (o (l+1)))
    (t : Fin (2*r+1)) :
    (∑ l, boolBit (o l))+matchingShared shared t =
      intrinsicChi edgeBits htrace+boolBit (Bool.xor (intrinsicTrace edgeBits htrace t) (o t)) := by
  rw [boolBit_xor]
  apply matching_tester_identity (fun l => boolBit (intrinsicTrace edgeBits htrace l))
    (fun l => boolBit (o l)) shared
  intro l
  have he := congrFun (intrinsicTrace_edges edgeBits htrace) l
  rw [hs,← he]
  change boolBit (Bool.xor _ _)+_+_=_
  rw [boolBit_xor]
  ring

/-- Ordinary functionals are read directly from the private outgoing component.
The old representation formula is a theorem, rather than a definition by descent. -/
theorem private_outgoing_cut {r : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (w : Fin (2*r+1) → W)
    (test : Fin (2*r+1) → Fin (2*r+1) → W →ₗ[ZMod 2] ZMod 2)
    (hprivate : ∀ l t, test l t (w (l+1))=0) (t : Fin (2*r+1)) :
    (∑ l, test l t (w l+w (l+1))) = ∑ l, test l t (w l) := by
  simp only [map_add,hprivate,add_zero]

end
end Lax793645Proofs.Simplifications
