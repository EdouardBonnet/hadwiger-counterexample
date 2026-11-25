/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.SparseCutProfiles.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RawFrameLaws

namespace Lax793645Proofs.Upstream.OAI

/-! # Sparse Cut Profiles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n : ℕ}

theorem Wtag_disabled {l d : Tag p.g} (h : ¬allowed d l) (t : Tag p.g) (i : Fin n)
    {m : Moment p n} (hm : m ∈ Wtag p n l) (s : SelIdx p.b p.j) (r : Row p n) :
    m (s,some (Block.O d t,i)) r = 0 := by
  unfold Wtag at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    change (selV _ _ _ * z _) * _ = 0
    rw [hz d t h,mul_zero,zero_mul]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy,add_zero]
  | smul a x _ h => simp only [Matrix.smul_apply,h,smul_zero]

/-- Intersect W_l over a strict majority. Every O coordinate is forced
to zero and projecting onto the shared variables fixes the matrix. -/
theorem Wtag_majority_star {I : Finset (Tag p.g)}
    (hI : p.g < 2 * I.card) {m : Moment p n} (h : ∀ l ∈ I, m ∈ Wtag p n l) :
    m ∈ Wstar p n := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hm : m ∈ Wspace p n := Wtag_le a (h a ha)
  have hz (s : SelIdx p.b p.j) (i : Fin n) (d t : Tag p.g) (r : Row p n) :
      m (s,some (Block.O d t,i)) r = 0 := by
    obtain ⟨l,hl,hg⟩ : ∃ l ∈ I, ¬allowed d l := by
      by_contra! he
      have hi := @Finset.card_le_card _ I (Finset.univ.filter (allowed d)) (by
        intro l hl; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he _ hl⟩)
      have hh := card_allowed d
      rw [Fintype.card_subtype] at hh
      have hi' := hi.trans_eq hh
      unfold privateWidth at hi'
      omega
    exact Wtag_disabled hg _ _ (h _ hl) _ _
  let kB : BaseIdx p.g n → F := fun i => i.1.elim (fun _ => 0) (fun _ => 1)
  let k : Row p n → F := fun i => Option.elim' 1 kB i.2
  let D := Matrix.diagonal k
  let L (z : Base p.g n) := fun i => kB i * z i
  have hL (s z) : D *ᵥ point p s z = point p s (L z) := by
    funext i
    simp only [D,Matrix.mulVec_diagonal]
    rcases i with ⟨s,i⟩
    rcases i with _|i
    · change (1:F)*_ = _
      rw [one_mul]; rfl
    change kB i * (selV _ _ _ * z i) = _ * (kB i * _); rw [mul_left_comm]
  have hx : liftM D D m ∈ Wstar p n := by
    clear h hz
    unfold Wspace at hm
    induction hm using Submodule.span_induction with
    | mem m he =>
      obtain ⟨s,z,rfl⟩ := he
      rw [mom,liftM_outer,hL]
      exact Submodule.subset_span ⟨s,L z,fun d t i => by
        change (0:F)*_=0
        rw [zero_mul],rfl⟩
    | zero => simp only [map_zero,Submodule.zero_mem]
    | add i j _ _ h g => rw [map_add]; exact Submodule.add_mem _ h g
    | smul _ _ _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  have hrow (i j) : k i*m i j = m i j := by
    rcases i with ⟨s,_|⟨⟨d,t⟩|a,i⟩⟩
    · exact one_mul _
    · rw [hz]
      simp
    · exact one_mul _
  have hj : liftM D D m = m := by
    ext i j
    simp only [liftM_def,D,Matrix.diagonal_transpose,Matrix.mul_diagonal,Matrix.diagonal_mul,hrow]
    rw [mul_comm]
    have heq : m i j=m j i := congr_fun (congr_fun (Wspace_sym hm) j) i
    rw [heq,hrow]
  rwa [hj] at hx

def totalRank (x : Profile p n) : ℕ := ∑ i, (x i).rank
def nonzeroTags (w : Tag p.g → Moment p n) : Finset (Tag p.g) :=
  by classical exact Finset.univ.filter (fun i => w i ≠ 0)

theorem mem_nonzeroTags (i) (w : Tag p.g → Moment p n) :
    i ∈ nonzeroTags w ↔ w i ≠ 0 := by classical simp [nonzeroTags]

theorem cut_const (w : Tag p.g → Moment p n) (m : Moment p n) :
    cut p n (fun i => w i+m) = cut p n w := by
  funext i
  change w _ + m + (w _ + m) = w _ + w _
  rw [add_add_add_comm, char_two,add_zero]

end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
