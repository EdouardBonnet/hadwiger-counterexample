/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.GradientRealization.
Changes: use protected tensor spaces for linear realization and key independence;
remove the selector-degree hypothesis. Channel compression is unchanged.
-/
import Lax793645Proofs.Simplifications.AffineResponseSolvability
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GradientRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N : ℕ}

/-- Reshaped pin rank cutoff needed by the protected-space argument. -/
def affineQorth (K : ℕ) := (Rorth K)^2+14

/-- Realization requires odd tag count and channel room, but no lower bound
on selector degree. The selected inputs instead satisfy `affineAvoids`. -/
structure AffineRealizeAssum (p : Shape) (K : ℕ) : Prop where
  odd : Odd p.g
  cap : rankAll p K+2*(K+2*(3*blin K)) ≤ p.h

variable {I : Type} [Fintype I]
namespace AffineRealization
set_option maxHeartbeats 600000 in
private theorem realize_one (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Plan p n) (T B : Cross p n)
    (K : ℕ) (h : AffineRealizeAssum p K)
    (hb : v.bounded w.obj) (ht : v.legal t)
    (hv : affineAvoids v a (affineQorth K)) (hK : planRank a≤K) (hL : planRank b≤K)
    (hB : fitsTable a b B T) (hT : tableInj a b T)
    (hf : rowAgree (v.frozen a t) B (actual p x y)) (hC : lowCross (blin K) B)
    (hR : v.scalarRecipe w t m x a T) (hk : v.keys t x=w.keys t y)
    (hy : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (j : Bool) :
    ∃ D∈deltaSpace p (v.frozen a t) b j,
      obsPair p (chanInner p (channelOut p B j+D) (channelOut p B j+D))=
        combineF p (v.demand w t m j) := by
  classical
  let G := v.demand w t m j
  let L := blin K
  let R := rankInit p
  obtain ⟨D,hD,P,hP,hZ⟩ := affine_realize_linear v w m x y a b T B hb ht (affineQorth K) (Rorth K) hv
    (by unfold Rorth; omega) (Nat.le_refl (affineQorth K)) hB hT hf hR hk hy hS j
  let C := channelOut p B j
  let f := v.frozen a t
  have he (z i) : dim (sPin f z i) ≤ K+14 :=
    (v.frozen_here_dim hb a t i z).trans (Nat.add_le_add_right hK 14)
  obtain ⟨M,hM,hA⟩ :
      ∃ M : Individual p n, obsI p M=combineF p G ∧ ∀ i e,(M i e).rank≤R := by
    choose M hM hA using fun i : Bool =>
      v.gradient_rep (w:=w.obj) (i:=i) (j:=j) m h.odd ht (hb _ _).2 (hR.summ i j)
    refine ⟨M,?_,hA⟩
    have he : repF p M=G := by
      funext i
      exact LinearMap.ext fun x => (repF_rep M i x).trans (hM i x).symm
    change combineF p (repF p M)=_
    rw [he]
  obtain ⟨D,Q,V,X,hV,hQ,hW,hU,hX,hG,hF,hE⟩ := split_linear R (K+14) L he hA
    (outSmall_low hC j) hD hP (hZ.trans hM.symm)
  obtain ⟨Q',hq,hO,hN⟩ := shrink_pure (K+14) K (rankRes K) he (fun z i => by
      unfold f; rw [v.hPin_frozen]; exact ((hPin_dim ..).trans (dim_le_plan a z)).trans hK)
    hE hQ hF
  have hJ (i) : ((Q'+V) i).rank≤rankAll p K := (mrk_add_le ..).trans ((add_le_add
    (hN i) (hX i)).trans_eq (add_comm _ _))
  obtain ⟨Z,hY,hZ⟩ := chan_factor (3*L) (rankAll p K) K hU
    (fun z => ((hPin_dim ..).trans (dim_le_plan b z)).trans hL) h.cap
    ((pureSpace p f).add_mem hq hW) hJ
  refine ⟨D+Z,(deltaSpace p f b j).add_mem hV hY,?_⟩
  rw [← add_assoc,hZ,map_add,hO,←map_add,hG,hM]

end AffineRealization

private theorem addChan_val (M : Cross p n) (D : Bool → ChanOut p n) (i : Bool) :
    channelOut p (M+addChan p D) i= channelOut p M i+D i := by
  funext z
  unfold addChan channelOut
  simp only [Fintype.sum_bool,Pi.add_apply,Matrix.transpose_add,Matrix.add_mul,Matrix.mul_assoc]
  cases i <;> simp only [IH_self,IH_cross (show false≠true by decide),
    IH_cross (show true≠false by decide),Matrix.mul_zero,Matrix.mul_one,transpose_zero,
    transpose_transpose,zero_add,add_zero]

private theorem addChan_zero {D : Bool → ChanOut p n} {f b : Plan p n}
    (h : ∀ i,D i∈deltaSpace p f b i) :
    zeroRow p f (addChan p D) ∧ zeroRow p b (reciprocal p (addChan p D)) := by
  have hh (z : Place p) (i : Bool) :=
    box_kill.mp ((deltaSpace_mem _).mp (h i) z)
  constructor
  · intro z v hv
    unfold addChan
    simp only [Fintype.sum_bool,transpose_add, transpose_mul,transpose_transpose,
      Matrix.add_mulVec,← Matrix.mulVec_mulVec,(hh z _).2 v hv,mulVec_zero,zero_add]
  intro z v hv
  unfold reciprocal addChan
  have ht (i) : (IH p n i)ᵀ *ᵥ v ∈ hPin b (flipZ p (flipZ p z)) i := by
    rw [flipZ_flip]; exact ⟨v,hv,rfl⟩
  have he i := (hh (flipZ p z) i).1 _ (ht i)
  simp only [Fintype.sum_bool, Matrix.transpose_transpose,Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec,he,zero_add]

private theorem recip_effect (B : Cross p n) (D : Bool → ChanOut p n) :
    scalarBlocks p (B+reciprocal p (addChan p D))=scalarBlocks p B := by
  funext z i j
  unfold scalarBlocks channelOut reciprocal addChan
  simp only [Pi.add_apply,Fintype.sum_bool,Matrix.transpose_add,Matrix.add_mul,Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.mul_assoc,IH_IP,Matrix.mul_zero,add_zero]

private theorem delta_frozen {b f : Plan p n} (v : Volley p n I) (t : Tagging p I) (i : Bool) :
    deltaSpace p f (v.frozen b t) i=deltaSpace p f b i := by
  unfold deltaSpace
  simp_rw [v.hPin_frozen]

private theorem recip_add (B C : Cross p n) :
    reciprocal p (B+C) = reciprocal p B+reciprocal p C := by
  funext i; exact Matrix.transpose_add _ _

namespace AffineRealization
private theorem realized_changes (v w : Volley p n I) (t : Tagging p I)
    (m : Mixer p n) {D E : Bool → ChanOut p n} {B : Cross p n}
    (h : ∀ j,obsPair p (chanInner p (channelOut p B j+D j) (channelOut p B j+D j))=
      combineF p (v.demand w t m j)) :
    v.realized w t m (B+addChan p D+reciprocal p (addChan p E)) := by
  intro i j x hx
  let B' := B+addChan p D
  have he := h j
  rw [← addChan_val B D j,obsPair_chan] at he
  rw [contract_scalars _ _ (recip_effect _ E)]
  exact ((combineF_same ..).mp he i x hx).symm
end AffineRealization

set_option maxHeartbeats 800000 in
theorem affine_gradient_realization (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Pin p n N) (T : Cross p n) (K : ℕ)
    (h : AffineRealizeAssum p K)
    (hA : v.bounded w.obj) (hB : w.bounded v.obj)
    (ht : v.legal t) (ht' : w.legal t)
    (hv : affineAvoids v a.sp (affineQorth K)) (hw : affineAvoids w b.sp (affineQorth K))
    (hK : planRank a.sp ≤ K) (hL : planRank b.sp ≤ K)
    (h1 : a.agree x) (h2 : b.agree y)
    (h3 : tableFlag a b T x) (h4 : tableFlag b a (reciprocal p T) y)
    (hT : tableInj a.sp b.sp T) (hT' : tableInj b.sp a.sp (reciprocal p T))
    (hR : v.scalarRecipe w t m x a.sp T) (hR' : w.scalarRecipe v t m y b.sp (reciprocal p T))
    (hk : v.keys t x=w.keys t y)
    (hx : ∀ i,frameLaw m (onSide x i)) (hy : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (hS' : w.attackGrad v t m x) :
    ∃ Q : Cross p n, v.realized w t m Q ∧ w.realized v t m (reciprocal p Q) ∧
    rowAgree (v.frozen a.sp t) Q (actual p x y) ∧
    rowAgree (w.frozen b.sp t) (reciprocal p Q) (actual p y x) := by
  classical
  obtain ⟨M,hQ,hD,hD',hM,hM'⟩ := start_form a b x y T
    (v.keyPlan t) (w.keyPlan t) (keyPlane v t) (keyPlane w t)
    (fun z => (affine_key_independent v t a.sp (affineQorth K) hv z).2.symm) (fun z => (affine_key_independent w t b.sp (affineQorth K) hw z).2.symm)
    h1 h2 h3 h4 K hK hL (v.key_dim hA t) (w.key_dim hB t)
  choose D hDA hG using fun j => AffineRealization.realize_one v w m x y a.sp b.sp T M K h
    hA ht hv hK hL hQ hT hD hM hR hk hy hS j
  choose E hEA hF using fun j => AffineRealization.realize_one w v m y x b.sp a.sp (reciprocal p T)
    (reciprocal p M) K h hB ht' hw hL hK (fits_recip hQ) hT' hD' hM' hR' hk.symm hx hS' j
  let Q := M+addChan p D+reciprocal p (addChan p E)
  have he : reciprocal p Q = reciprocal p M+addChan p E+reciprocal p (addChan p D) := by
    unfold Q
    rw [recip_add,recip_add,reciprocal_twice]; ac_rfl
  obtain ⟨hN,hN'⟩ := addChan_zero (D:=D) (f:=v.frozen a.sp t) (b:=w.frozen b.sp t)
    (fun i => by rw [delta_frozen w t i]; exact hDA i)
  obtain ⟨hO,hO'⟩ := addChan_zero (D:=E) (f:=w.frozen b.sp t) (b:=v.frozen a.sp t)
    (fun i => by rw [delta_frozen v t i]; exact hEA i)
  refine ⟨Q,AffineRealization.realized_changes v w t m hG,?_,row_add (row_add hD hN) hO',?_⟩
  · rw [he]
    exact AffineRealization.realized_changes w v t m hF
  rw [he]; exact row_add (row_add hD' hO) hN'

end
end Lax793645Proofs.Simplifications
