import Lax793645Proofs.Simplifications.OnePhaseCompatibility
import Lax793645Proofs.Simplifications.RowSupportProbability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset PredictionClass
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

/-- For independent units, any zero parity between two readings of the
same listener has polynomial mass even before constructing a cover. -/
theorem one_reciprocal_zero (S : Party) (Δ : OneUnit p n N → Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) :
    1 / (4 * ((2 * dim (Ambient p (2*N)) : ℕ) + 1 : ℝ)) ≤
      pr (pairW w w) (fun x =>
        joinPhase p (oneListens x.2) S (Δ x.1) +
        joinPhase p (oneListens x.1) S (Δ x.2) = 0) := by
  let M : Mat (OneUnit p n N) (OneUnit p n N) :=
    Matrix.of (fun x y => joinPhase p (oneListens y) S (Δ x))
  have hM : M.rank ≤ dim (Ambient p (2*N)) :=
    dual_matrix_rank Δ (fun x => joinPhase p (oneListens x) S)
  have hsum : (M + Mᵀ).rank ≤ 2 * dim (Ambient p (2*N)) := by
    have h := mrk_add_le M Mᵀ
    rw [Matrix.rank_transpose] at h
    omega
  exact zero_entry_probability (M+Mᵀ) w hw _ hsum (fun x => char_two _)

theorem one_ambient_dimension (hg : 3 ≤ p.g) :
    dim (Ambient p (2*N)) = p.g * (2*N) * (2*N) := by
    change Module.finrank F (Comp p.g → Mat (Fin (2*N)) (Fin (2*N))) = _
    rw [Module.finrank_pi_fintype]
    simp [show Module.finrank F (Mat (Fin (2*N)) (Fin (2*N))) =
        (2*N) * (2*N) by simpa using dim_mat (Fin (2*N)) (Fin (2*N)),
      CycleGeometry.card_comp hg, Nat.mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The equal active prediction class, expressed using the construction's
actual compatibility predicate. Here g is the number of cycle components. -/
theorem one_twinned_ambient_mass (hg : 3 ≤ p.g)
    (α : Party) (r : F) (Δ : OneUnit p n N → Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) :
    1 / (4 * ((2 * (p.g * (2*N) * (2*N)) : ℕ) + 1 : ℝ)) ≤
      pr (pairW w w) (oneMatchUp Δ α r twinned) := by
  have h := one_reciprocal_zero allSide Δ w hw
  rw [one_ambient_dimension (N:=N) hg] at h
  convert h using 1
  apply congrArg (pr (pairW w w))
  funext x
  unfold oneMatchUp compatible oneQuench
  dsimp only
  rw [← one_tone_vec, ← one_tone_vec]

set_option maxHeartbeats 1000000 in
/-- A single active endpoint with zero prescribed reciprocal parity. -/
theorem one_singleton_ambient_mass (α : Party) (i : Bool) (hα : α i = 1)
    (r : F) (Δ : OneUnit p n N → Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) :
    1 / (4 * ((2 * dim (Ambient p (2*N)) : ℕ) + 1 : ℝ)) ≤
      pr (pairW w w) (oneMatchUp Δ α r (dawn i)) := by
  have h := one_reciprocal_zero (unary i) Δ w hw
  convert h using 1
  apply congrArg (pr (pairW w w))
  funext x
  unfold oneMatchUp compatible oneQuench
  dsimp only
  rw [firstBit, hα, char_two]

/-- The denominator uses the dimension of the ambient matrix space only.
The orientations are independent draws from any single law. -/
theorem one_zero_parity_mass (hg : 3≤p.g) (hN : 1≤(2*N:ℕ)) (c : PredictionClass)
    (α : Party) (r : F) (Δ : OneUnit p n N→Ambient p (2*N)) (v : Wgt (OneUnit p n N))
    (hv : IsLaw v) (hc : c=twinned ∨ ∃ i,c=dawn i ∧ α i=1) :
    (1/(4*(2*(p.g:ℝ)+1)))/((2*N:ℕ):ℝ)^2 ≤ pr (pairW v v) (oneMatchUp Δ α r c) := by
  have h : 1/(4*((2*(p.g*(2*N)*(2*N)):ℕ)+1:ℝ)) ≤ pr (pairW v v) (oneMatchUp Δ α r c) := by
    rcases hc with rfl|⟨i,rfl,hi⟩
    · exact one_twinned_ambient_mass hg α r Δ v hv
    rw [←one_ambient_dimension (N:=N) hg]
    exact one_singleton_ambient_mass α i hi r Δ v hv
  refine le_trans ?_ h
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  have hz : 1≤((2*N:ℕ):ℝ) := by exact_mod_cast hN
  have hz2 : 1≤((2*N:ℕ):ℝ)^2 := by nlinarith only [hz,sq_nonneg (((2*N:ℕ):ℝ)-1)]
  push_cast at hz2 ⊢
  nlinarith only [hz2]

theorem one_zero_parity_quartic_mass (hg : 3≤p.g) (hN : 1≤(2*N:ℕ)) (c : PredictionClass)
    (α : Party) (r : F) (Δ : OneUnit p n N→Ambient p (2*N)) (w : Wgt (OneUnit p n N))
    (hw : IsLaw w) (hc : c=twinned ∨ ∃ i,c=dawn i ∧ α i=1) :
    (1/(4*(2*(p.g:ℝ)+1)))/((2*N:ℕ):ℝ)^4 ≤ pr (pairW w w) (oneMatchUp Δ α r c) := by
  refine le_trans ?_ (one_zero_parity_mass hg hN c α r Δ w hw hc)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_right₀ (by exact_mod_cast hN) (by decide : 2≤4)

def oneWeightedCover (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (x : OneUnit p n N) : coverX p T :=
  open scoped Classical in
  if w x=0 then 0 else oneCoverDelta T Δ x

def oneShadow (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (x y : OneUnit p n N) (S : Party) :=
  oneJuris T y S (oneWeightedCover T Δ w x)

theorem one_shadow_valid (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    {w : Wgt (OneUnit p n N)} (h : ∀ x,w x≠0→covered p T (Δ x))
    (x y : OneUnit p n N) (S : Party) (hx : w x≠0) :
    oneShadow T Δ w x y S=joinPhase p (oneListens y) S (Δ x) := by
  classical
  simp only [oneShadow,oneWeightedCover,if_neg hx,oneCoverDelta,dif_pos (h x hx)]
  rfl

def oneCircus (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) : Mat (OneUnit p n N) (OneUnit p n N) :=
  fun x y=>oneShadow T Δ w x y allSide

theorem one_circus_rank (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) : (oneCircus T Δ w).rank≤(2*N)*cdim p T :=
  (dual_matrix_rank (oneWeightedCover T Δ w) (fun y=>oneJuris T y allSide)).trans (cover_dim p T)

/-- In the equal nonzero prediction class, an alternating low-rank
matrix gives polynomial compatibility without an entropy fiber. -/
theorem one_twinned_rank_compatibility (T : Cov p (2*N)) (d : ℕ) (hd : cdim p T≤d)
    (α : Party) (r : F) (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w)
    (hcover : ∀ x,w x≠0→covered p T (Δ x)) :
    1/(4*(2*d*(2*N)+1):ℝ)≤pr (pairW w w) (oneMatchUp Δ α r twinned) := by
  let M:=oneCircus T Δ w
  have hm : M.rank≤(2*N)*d:=(one_circus_rank T Δ w).trans (Nat.mul_le_mul_left _ hd)
  have hr : (M+Mᵀ).rank≤2*d*(2*N) := by
    have hh:=mrk_add_le M Mᵀ
    rw [Matrix.rank_transpose] at hh
    nlinarith only [hm,hh]
  have hh:=zero_entry_probability (M+Mᵀ) w hw (2*d*(2*N)) hr (fun x=>char_two _)
  have he : pr (pairW w w) (fun x=>(M+Mᵀ) x.1 x.2=0)=
      pr (pairW w w) (oneMatchUp Δ α r twinned) := by
    apply avg_congr
    intro x hx
    apply congrArg ind
    apply propext
    unfold oneMatchUp compatible oneQuench
    dsimp only
    rw [←one_tone_vec,←one_tone_vec]
    change (oneShadow T Δ w x.1 x.2 allSide+oneShadow T Δ w x.2 x.1 allSide=0)↔_
    rw [one_shadow_valid T Δ hcover _ _ _ (left_ne_zero_of_mul hx),
      one_shadow_valid T Δ hcover _ _ _ (right_ne_zero_of_mul hx)]
  rw [he] at hh
  exact_mod_cast hh

/-- A finite label for each unit determines a relation on pairs. The bound
counts labels in either coordinate, including after transposing the test. -/
structure PairCode (A : Type) (budget : ℝ) where
  count : ℕ
  fits : (count:ℝ)≤budget
  label : A→Fin count
  test : Fin count × Fin count → Prop

def PairCode.read {A : Type} {B : ℝ} (c : PairCode A B) (v : A×A) :=
  c.test (c.label v.1,c.label v.2)

theorem PairCode.named_both {A : Type} {B : ℝ} (c : PairCode A B) :
    named c.read B ∧ named (c.read ∘ Prod.swap) B := by
  refine ⟨⟨c.count,c.fits,fun j x=>c.test (c.label x,j),fun y=>⟨c.label y,fun _=>Iff.rfl⟩⟩,
    c.count,c.fits,fun j x=>c.test (j,c.label x),fun y=>⟨c.label y,fun _=>Iff.rfl⟩⟩

/-- Only the linear span of the offsets matters. A unit records its offset
and the restrictions of its two listeners to this span. -/
theorem one_offset_span_code (V : Space (Ambient p (2*N))) (d : ℕ)
    (hd : dim V≤(2*N)*d) (c : PredictionClass) (α : Party) (r : F)
    (Δ : OneUnit p n N→Ambient p (2*N)) :
    ∃ code : PairCode (OneUnit p n N) (bp (3*d*(2*N:ℝ))),∀ x y,
      Δ x∈V → Δ y∈V → (code.read (x,y) ↔ oneMatchUp Δ α r c (x,y)) := by
  classical
  letI : Fintype (Module.Dual F V):=Fintype.ofInjective
    (fun f=>(f : V→F)) DFunLike.coe_injective
  let A:=V × (Bool → Module.Dual F V)
  have he : dim A≤3*d*(2*N) := by
    unfold A dim
    rw [finrank_prod,finrank_pi_fintype,Fintype.sum_bool,Subspace.dual_finrank_eq]
    change dim V+(dim V+dim V)≤_
    nlinarith only [hd]
  have hc : num A≤bp (3*d*(2*N:ℝ)) := by
    unfold num
    rw [card_space]
    exact bp_le (by exact_mod_cast he)
  let Q (x : A×A) := c.compatible α r (fun i=>x.2.2 i x.1.1,fun i=>x.1.2 i x.2.1)
  let f (x : OneUnit p n N) : A :=
    (if h : Δ x∈V then ⟨Δ x,h⟩ else 0,fun i=>(joinPhase p (oneListens x) (unary i)).comp V.subtype)
  let e:=Fintype.equivFin A
  refine ⟨⟨Fintype.card A,hc,e ∘ f,fun ij=>Q (e.symm ij.1,e.symm ij.2)⟩,?_⟩
  intro x y hx hy
  change Q (e.symm (e (f x)),e.symm (e (f y))) ↔ _
  rw [e.symm_apply_apply,e.symm_apply_apply]
  simp only [Q,f,dif_pos hx,dif_pos hy,oneMatchUp,oneQuench,LinearMap.comp_apply,
    Submodule.subtype_apply]

end
end Lax793645Proofs.Simplifications
