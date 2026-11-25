/- Adapts the finite probe-growth argument from the vendored Apache-2.0
OpenAI AdditionalProbeBounds module to symmetric offsets. -/
import Lax793645Proofs.Simplifications.OneFrequentPhaseTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def symTotal (p : Shape) (q : Comp p.g→ℕ) :=∑ e,q e
def symOffsetCover {p : Shape} {N r : ℕ} {T : SymCover p N} (M : SymAtlas p r T) : SymCover p N:=
  fun e=>colSp (symSrc M e)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

private def moreMatrix {r : ℕ} (A : Mat I (Fin r)) (v : Vec I) : Mat I (Fin (r+1)) :=
  Matrix.of (fun i => Fin.cons (v i) (A i))

omit [Fintype I] in
private theorem moreMatrix_act {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (x : Vec (Fin (r+1))) :
    moreMatrix A v *ᵥ x=x 0 • v + A *ᵥ (fun i => x i.succ) := by
  funext i; simp only [Matrix.mulVec,dotProduct,moreMatrix,Matrix.of_apply,
    Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fin.cons_zero,Fin.cons_succ]
  congr 1; exact mul_comm _ _

omit [Fintype I] in
private theorem moreMatrix_inj {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (ha : Injective A.mulVec) (h : v∉colSp A) :
    Injective (moreMatrix A v).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  rw [moreMatrix_act] at hx
  let b (i : Fin r) := x i.succ
  rcases bit_cases (x 0) with he|he
  · have hh : b=0 := by
      apply ha
      rw [he,zero_smul,zero_add] at hx
      exact hx.trans (Matrix.mulVec_zero _).symm
    funext i
    refine Fin.cases he (fun k => ?_) i
    exact congr_fun hh k
  · rw [he,one_smul] at hx
    have heq : v=A *ᵥ b := add_right_cancel (hx.trans (char_two _).symm)
    exact (h ⟨b,heq.symm⟩).elim

omit [Fintype J] in
private theorem moreMatrix_mul {r} (B : Mat J I) (A : Mat I (Fin r)) (v) :
    B*moreMatrix A v=moreMatrix (B*A) (B *ᵥ v) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  simp only [moreMatrix,Matrix.mul_apply,Matrix.of_apply,Fin.cons_succ]

variable {p : Shape} {n N r : ℕ} {T : SymCover p (2*N)}
variable {q : Comp p.g → ℕ}

private def growFmt (q : Comp p.g→ℕ) (z : Comp p.g) := fun i =>
  q i+(if i=z then 1 else 0)

private theorem grow_sum (q : Comp p.g→ℕ) (z : Comp p.g) :
    symTotal p (growFmt (p:=p) q z)=symTotal p q+1 := by simp [growFmt,symTotal,Finset.sum_add_distrib]

private def growing (A : ImageTuple (Comp p.g) q (2*N)) (z : Comp p.g) (v : Vec (Fin (2*N))) :
    ImageTuple (Comp p.g) (growFmt (p:=p) q z) (2*N) := fun i => by
  change Mat (Fin (2*N)) (Fin (q i+ if i=z then 1 else 0))
  by_cases h : i=z
  · rw [if_pos h]; exact moreMatrix (A i) v
  rw [if_neg h]; exact A i

private theorem castMat_inj {r n m : ℕ} (e : r=n)
    (A : Mat (Fin m) (Fin r)) (h : Injective A.mulVec) :
    Injective (cast (show Mat (Fin m) (Fin r)=Mat (Fin m) (Fin n) from congrArg (fun t => Mat (Fin m) (Fin t)) e) A).mulVec := by
  subst n
  exact h
private theorem castMat_prod {r n m : ℕ} (e : r=n)
    (A : Mat (Fin m) (Fin r)) (B : Mat (Fin m) (Fin m)) :
    B*(cast (show Mat (Fin m) (Fin r)=Mat (Fin m) (Fin n) from congrArg (fun t => Mat (Fin m) (Fin t)) e) A) =
    cast (show Mat (Fin m) (Fin r)=Mat (Fin m) (Fin n) from congrArg (fun t => Mat (Fin m) (Fin t)) e) (B*A) := by
  subst n; rfl

private theorem growth_inj (A : ImageTuple (Comp p.g) q (2*N)) (z : Comp p.g) (v : Vec (Fin (2*N)))
    (hv : v∉colSp (A z)) (h : ∀ i, Injective (A i).mulVec) :
    ∀ i,Injective (growing A z v i).mulVec := by
  intro i
  by_cases he : i=z
  · subst i
    simp [growing,growFmt]
    apply castMat_inj _ (moreMatrix (A z) v) (moreMatrix_inj (A z) v (h z) hv)
    simp
  simp [growing,growFmt,he]
  apply castMat_inj _ (A i) (h i)
  simp [he]

private theorem growth_value (A : ImageTuple (Comp p.g) q (2*N)) (z : Comp p.g) (v : Vec (Fin (2*N)))
    (x : OneUnit p n N) (S : Party) :
    oneThermal x S (growing A z v)=growing (oneThermal x S A) z ((oneHeat x S z+(oneHeat x S z)ᵀ) *ᵥ v) := by
  funext i
  by_cases he : i=z
  · subst i
    simp [oneThermal,growing,growFmt]
    rw [←moreMatrix_mul]
    apply castMat_prod
    simp
  simp [oneThermal,growing,growFmt,he]
  apply castMat_prod
  simp [he]

theorem column_observe (A : ImageTuple (Comp p.g) q (2*N)) (z : Comp p.g) (j : Fin (q z))
    (x : OneUnit p n N) (S : Party) :
    (oneHeat x S z+(oneHeat x S z)ᵀ) *ᵥ (A z).col j=(oneThermal x S A z).col j := rfl

namespace OneBazaar
variable (s : OneBazaar p n r T)

abbrev Catalog (p : Shape) {N} (T : SymCover p N) (r : ℕ) (q : Comp p.g→ℕ) :=
  (M : SymAtlas p r T) → SymBatch M N → Finset (ImageTuple (Comp p.g) q N)

def atList (s : OneBazaar p n r T) (S : Party) (j : Bool)
    (A : ImageTuple (Comp p.g) q (2*N)) (F : Catalog p T r q) (x : OneUnit p n N) :=
  let M := s.ix x
  oneThermal x S A∈ F M (s.bag M j x)

def probed (p : Shape) {N} {q : Comp p.g→ℕ} (A : ImageTuple (Comp p.g) q (2*N)) : SymCover p (2*N) :=
  fun z => colSp (A z)

theorem extend_probe (w : Wgt (OneUnit p n N)) (S : Party) (j : Bool) {k : ℕ}
    (A : ImageTuple (Comp p.g) q (2*N)) (hq : symTotal p q=k)
    (h : ∀ i, Injective (A i).mulVec)
    (F : Catalog p T r q) (hF : ∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*(2*N)))
    (G : SymAtlas p r T) (hg : ¬ symOffsetCover G ≤ probed p A)
    (hb : ∀ M Z,(↑(s.bids w S j G M Z).card:ℝ) ≤ bp (0.51*(2*N))) :
    ∃ (q : Comp p.g→ℕ) (A' : ImageTuple (Comp p.g) q (2*N))
      (F' : Catalog p T r q), symTotal p q=k+1 ∧
      (∀ i, Injective (A' i).mulVec) ∧
      (∀ M Z,(↑(F' M Z).card:ℝ) ≤ bp (0.51*(k+1)*(2*N))) ∧
      ∀ x,s.atList S j A F x → s.frequent w S j G (s.ix x) x →
        s.atList S j A' F' x := by
  classical
  obtain ⟨z,i,hg⟩ :
      ∃ (z : Comp p.g) (i : Fin (symBreadth G z)),(symSrc G z).col i∉colSp (A z) := by
    by_contra! hh
    apply hg
    intro z
    change colSp (symSrc G z) ≤ _
    rw [colSp,range_mulVecLin]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr (hh z))
  let q' := growFmt (p:=p) q z
  let v := (symSrc G z).col i
  let f (M Z) : Finset (ImageTuple (Comp p.g) q' (2*N)) :=
    ((F M Z) ×ˢ (s.bids w S j G M Z)).image
      (fun a => growing a.1 z ((a.2 z).col i))
  refine ⟨q',growing A z v, f,(grow_sum q z).trans (by rw [hq]),
    growth_inj A z v hg h,fun M Z => ?_,fun x hx hi => ?_⟩
  · have he := bp_pos (0.51*(k:ℝ)*(2*N))
    have h1 :
        (↑(f M Z).card:ℝ) ≤ (↑(F M Z).card:ℝ)*(↑(s.bids w S j G M Z).card:ℝ) := by
      exact_mod_cast (show (f M Z).card ≤ _*_ from
        Finset.card_image_le.trans_eq (Finset.card_product ..))
    apply (h1.trans (mul_le_mul (hF M Z) (hb M Z) (Nat.cast_nonneg _) he.le)).trans_eq
    rw [←bp_add]; congr 1; ring
  · rw [atList,growth_value]

    refine Finset.mem_image.mpr ⟨(oneThermal x S A,oneThermal x S (symSrc G)),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨hx,(s.bids_mem ..).mp hi⟩
    · change growing _ _ _ = _
      rw [show (oneHeat x S z+(oneHeat x S z)ᵀ) *ᵥ v=_ from column_observe (symSrc G) z i x S]

end OneBazaar
end
end Lax793645Proofs.Simplifications
