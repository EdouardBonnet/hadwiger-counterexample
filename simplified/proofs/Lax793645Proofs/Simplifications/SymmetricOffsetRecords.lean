import Lax793645Proofs.Simplifications.SymmetricOffsets
import Lax793645Proofs.Simplifications.QuadraticPhaseActions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.OffsetRecords

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev SymCover (p : Shape) (N : ℕ) := Comp p.g→Space (Vec (Fin N))
abbrev SymWidths (p : Shape) (r : ℕ) := Comp p.g→Fin (r+1)
abbrev SymOffsetBasis (p : Shape) (r : ℕ) {N : ℕ} (S : SymCover p N) (q : SymWidths p r) :=
  ∀ e,Mat (Fin (dim (S e))) (Fin (q e).val)
abbrev SymOffsetCost (p : Shape) (r : ℕ) (q : SymWidths p r) :=
  ∀ e : Comp p.g,Mat (Fin (q e).val) (Fin (q e).val)
abbrev SymAtlas (p : Shape) (r : ℕ) {N : ℕ} (S : SymCover p N) :=
  Σ q : SymWidths p r,SymOffsetBasis p r S q×SymOffsetCost p r q

instance symAtlasFintype {p : Shape} {r N : ℕ} (S : SymCover p N) : Fintype (SymAtlas p r S) := by
  classical
  exact inferInstanceAs (Fintype (Σ q : SymWidths p r,SymOffsetBasis p r S q×SymOffsetCost p r q))

instance symAtlasInhabited {p : Shape} {r N : ℕ} (S : SymCover p N) : Inhabited (SymAtlas p r S) :=
  ⟨⟨fun _=>0,0,0⟩⟩

variable {p : Shape} {r N : ℕ} {S : SymCover p N}

abbrev symBreadth (X : SymAtlas p r S) :=fun e : Comp p.g=>(X.1 e).val
def symCells (X : SymAtlas p r S) :=∑ e,symBreadth X e
abbrev SymBatch (X : SymAtlas p r S) (n : ℕ) :=∀ e,Mat (Fin n) (Fin (symBreadth X e))
def symSrc (X : SymAtlas p r S) : SymBatch X N:=fun e=>pack (S e)*X.2.1 e
def symEdgeCost (X : SymAtlas p r S) : Ambient p N:=fun e=>symSrc X e*X.2.2 e*(symSrc X e)ᵀ
def symSpelled (X : SymAtlas p r S) (Z : SymBatch X N) : Ambient p N:=
  fun e=>symSrc X e*(Z e)ᵀ+Z e*(symSrc X e)ᵀ+symEdgeCost X e
def symStandard (X : SymAtlas p r S) : Prop:=
  symCells X≠0 ∧symCells X≤r ∧(∀ e,Injective (symSrc X e).mulVec) ∧∀ e,(X.2.2 e)ᵀ=X.2.2 e
def symCompFor (X : SymAtlas p r S) (Z : SymBatch X N) (V : SymCover p N)
    (Δ : Ambient p N) : Prop:=
  (∀ e,Injective (Z e).mulVec ∧colSp (Z e)≤V e) ∧Δ=symSpelled X Z

/-- The symmetric construction has at most r companion columns in
total, and both endpoints use the same finite offset record. -/
theorem symmetric_profile_offsets (M : Bool→Ambient p N) (V : Bool→SymCover p N)
    (hsym : ∀ i e,(M i e)ᵀ=M i e) (hM : ∀ i e,M i e∈box (V i e) (V i e))
    (hSV : ∀ i e,Disjoint (S e) (V i e))
    (hz : ∀ e,vanish (S e) (S e) (M true e+M false e))
    (hne : M true+M false≠0) (hr : epoch p (M true)≤r) :
    ∃ X : SymAtlas p r S,symStandard X ∧
      ∀ i,∃ Z,symCompFor X Z (V i) (M true+M false) := by
  classical
  choose k T H hk hT hTS hH hZ using fun e=>symmetric_offsets
    (fun i=>M i e) (S e) (fun i=>V i e) (fun i=>hsym i e)
    (fun i=>hM i e) (fun i=>hSV i e) (hz e)
  have hkr (e) : k e≤r:=(hk e).trans
    ((Finset.single_le_sum (fun e _=>Nat.zero_le (M true e).rank) (Finset.mem_univ e)).trans hr)
  choose A hA using fun e=>pull_cols (pack (S e)) (T e) (by rw [colSp_pack]; exact hTS e)
  let X : SymAtlas p r S:=⟨fun e=>⟨k e,Nat.lt_succ_of_le (hkr e)⟩,A,H⟩
  have hsrc (e) : symSrc X e=T e:=hA e
  have hcomp (i) : ∃ Z,symCompFor X Z (V i) (M true+M false) := by
    choose Z hZi hZV hD using fun e=>hZ e i
    refine ⟨Z,fun e=>⟨hZi e,hZV e⟩,?_⟩
    funext e
    change M true e+M false e=symSrc X e*(Z e)ᵀ+Z e*(symSrc X e)ᵀ+symSrc X e*H e*(symSrc X e)ᵀ
    rw [hsrc]
    exact hD e
  refine ⟨X,⟨?_,?_,fun e=>hsrc e ▸ hT e,fun e=>hH e⟩,hcomp⟩
  · intro hzero
    have he (e) : k e=0:=Nat.eq_zero_of_le_zero
      ((Finset.single_le_sum (fun e _=>Nat.zero_le (k e)) (Finset.mem_univ e)).trans hzero.le)
    obtain ⟨Z,_,hZ⟩:=hcomp true
    apply hne
    rw [hZ]
    funext e
    let : IsEmpty (Fin (symBreadth X e)):=by change IsEmpty (Fin (k e)); rw [he]; infer_instance
    ext a b
    simp [symSpelled,symEdgeCost,Matrix.mul_apply]
  · exact (Finset.sum_le_sum (fun e _=>hk e)).trans hr

theorem sym_atlas_size (S : SymCover p N) (r : ℕ) :
    num (SymAtlas p r S)≤num (SymWidths p r)*
      bp ((∑ e,dim (S e))*r+num (Comp p.g)*r*r) := by
  classical
  unfold num SymAtlas
  rw [Fintype.card_sigma,Nat.cast_sum]
  have hh (q : SymWidths p r) :
      (Fintype.card (SymOffsetBasis p r S q×SymOffsetCost p r q):ℝ)≤
        bp ((∑ e,dim (S e))*r+(Fintype.card (Comp p.g):ℝ)*r*r) := by
    rw [card_space]
    apply bp_le
    have hA : dim (SymOffsetBasis p r S q)≤(∑ e,dim (S e))*r := by
      unfold dim SymOffsetBasis
      rw [finrank_pi_fintype,Finset.sum_mul]
      exact Finset.sum_le_sum (fun e _=>(dim_mat ..).trans_le (by
        rw [Fintype.card_fin,Fintype.card_fin]
        exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (q e).isLt)))
    have hH : dim (SymOffsetCost p r q)≤Fintype.card (Comp p.g)*r*r := by
      unfold dim SymOffsetCost
      rw [finrank_pi_fintype]
      calc
        _≤∑ _ : Comp p.g,r*r:=by
          apply Finset.sum_le_sum
          intro e _
          apply (dim_mat ..).trans_le
          simp only [Fintype.card_fin]
          exact Nat.mul_le_mul (Nat.lt_succ_iff.mp (q e).isLt) (Nat.lt_succ_iff.mp (q e).isLt)
        _ = _ := by simp [mul_assoc]
    have h:=Nat.add_le_add hA hH
    unfold dim at *
    rw [finrank_prod]
    exact_mod_cast h
  exact (Finset.sum_le_sum (fun q _=>hh q)).trans_eq (by simp)

end
end Lax793645Proofs.Simplifications
