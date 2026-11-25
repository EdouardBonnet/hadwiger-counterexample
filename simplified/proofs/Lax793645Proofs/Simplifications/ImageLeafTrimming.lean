/- Finite restriction lemmas adapted from the vendored Apache-2.0
PartitionSelection proof; closed pins are retained unchanged. -/
import Lax793645Proofs.Simplifications.ImageLeafMixtures

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I]
  {N c : ℕ} {X : A→C→Mat (Fin N) I} {cl : ImageClosure C I c} {w μ : Wgt A}

theorem image_ripe_restrict (hw : ∀ x,0≤w x) {S Y} {a : ImagePin C I N} {D ζ : ℝ} {K : ℕ}
    (h : ImageRipe X cl w μ S a D ζ K) (hz : 0≤ζ) (he : Y⊆S)
    (hp : bp (-ζ*N) ≤ partMass (partW w S) Y) :
    ImageRipe X cl w μ Y a (D+ζ) (2*ζ) K := by
  classical
  let v := partW w S
  have hv : IsLaw v := on_law hw h.pos
  have ht := lt_of_lt_of_le (bp_pos _) hp
  have hh := on_mon hv.nz (bp_pos _) hp
  obtain ⟨h1,h2⟩ := issued_law w hw h.pos he ht
  have hk (x) : partW w Y x ≤ bp (ζ*N) * v x := by
    rw [h2]
    have hg := hh x
    rw [neg_mul,bp_neg, inv_inv] at hg
    exact hg
  have hy : IsLaw (partW w Y) := on_law hw h1
  refine ⟨h1,fun x hx => h.fixpin x (he hx),h.closed,h.bound,fun b => ?_,fun x => ?_⟩
  · let r := imagePlanRank (a.sp⊔b.sp)-imagePlanRank a.sp
    by_cases hr : r=0
    · change pr _ _ ≤ fee N _ r
      rw [hr]
      simp only [fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero]
      exact (pr_le_tot hy.nz).trans hy.total.le
    apply ((pr_cap hk _).trans
      (mul_le_mul_of_nonneg_left (h.clear b) (bp_pos _).le)).trans
    change bp (ζ*N)*fee N ζ r ≤ fee N (2*ζ) r
    rw [fee,fee,←bp_add]
    apply bp_le
    have hh : 1≤(r:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have he := mul_le_mul_of_nonneg_right hh (mul_nonneg hz
      (show 0≤(N:ℝ) from Nat.cast_nonneg _))
    linarith only [he]
  exact ((hk x).trans (mul_le_mul_of_nonneg_left (h.density x) (bp_pos _).le)).trans_eq
    (by rw [add_mul,bp_add]; ring)

theorem image_trim (P : A→Prop) (hw : ∀ x,0≤w x) {D ζ : ℝ} (hz : 0≤ζ) {K}
    {T : Tiles A} (hT : apart T) (g : Finset A → ImagePin C I N)
    (h : ∀ i∈T,ImageRipe X cl w μ i (g i) D ζ K) :
    ∃ V : Tiles A,apart V ∧
    (∀ S∈V,∃ i∈T,S⊆i ∧ ImageRipe X cl w μ S (g i) (D+ζ) (2*ζ) K ∧ ∀ x∈S,P x) ∧
    pr w (fun x => inTiles T x ∧ P x ∧ ¬inTiles V x) ≤ allMass w T*bp (-ζ*N) := by
  classical
  refine improve T w hw P (fun i S => ImageRipe X cl w μ S (g i) (D+ζ) (2*ζ) K ∧ ∀ x∈S,P x)
    hT (fun i hi => ?_)
  let S := i.filter P
  have hs : S⊆i := Finset.filter_subset _ _
  let v := partW w i
  by_cases he : bp (-ζ*N) ≤ partMass v S
  · refine ⟨{S},?_,?_,?_⟩
    · intro x S h T h'; rw [mem_singleton.mp h,mem_singleton.mp h']; simp only [implies_true]
    · intro j hj; rw [mem_singleton.mp hj]
      exact ⟨hs,image_ripe_restrict hw (h i hi) hz hs he,fun x h => (mem_filter.mp h).2⟩
    have hh : (fun x => x∈i∧ P x∧ ¬inTiles ({S}:Tiles _) x)=(fun _ => False) := by
      ext x; simp [S,inTiles]; tauto
    rw [hh,pr_false]; exact (bp_pos _).le
  refine ⟨∅,by intro x S h; simp at h, by simp,?_⟩
  have hh (x : A) : x∈S ↔ x∈i∧ P x := by simp [S]
  have hn := le_of_not_ge he
  unfold partMass at hn
  simp_rw [hh] at hn
  simpa [inTiles,v] using hn

namespace ImageLeafMixture
variable {D ζ : ℝ} {K : ℕ}

def elder (s t : ImageLeafMixture A C I N) (P : A→Prop)
    (S : Finset A → Finset A → Prop) :=
  ∀ i ∈ t.T, ∃ i'∈ s.T,i⊆i' ∧ (∀ x∈i,P x) ∧ S i i'
theorem ancestral {s t : ImageLeafMixture A C I N} {P Q}
    (he : elder s t P Q) {x} (h : inTiles t.T x) : inTiles s.T x∧P x := by
  obtain ⟨j,hj,hx⟩ := h
  obtain ⟨i,hi,hs,hp,_⟩ := he j hj
  exact ⟨⟨_,hi,hs hx⟩,hp x hx⟩
theorem elder_trim {s : ImageLeafMixture A C I N} (h : s.strength X cl w μ D ζ K) (hz : 0≤ζ)
    (hw : IsLaw w) (P : A→Prop) :
    ∃ t : ImageLeafMixture A C I N, t.strength X cl w μ (D+ζ) (2*ζ) K ∧
      elder s t P (fun i j=>t.pin i=s.pin j) ∧
      pr w (fun x=>inTiles s.T x∧P x∧¬inTiles t.T x)≤ bp (-ζ*N) := by
  classical
  obtain ⟨T,ht,hg,hf⟩:= image_trim (X:=X) (cl:=cl) P hw.nz hz h.part s.pin h.leaf
  let f (i : Finset A) := if hi:i∈T then (hg i hi).choose else ∅
  let t : ImageLeafMixture A C I N := ⟨T,fun i=>s.pin (f i)⟩
  have he (i : Finset A) (hi : i∈T) :
      f i∈s.T ∧ i⊆ f i ∧ ImageRipe X cl w μ i (s.pin (f i)) (D+ζ) (2*ζ) K ∧ ∀ x∈i,P x := by
    unfold f; rw [dif_pos hi]; exact (hg i hi).choose_spec
  exact ⟨t,⟨ht,fun i hi=>(he i hi).2.2.1⟩,fun i hi=>by
    obtain ⟨h,h1,h2,h3⟩:= he i hi; exact ⟨_,h,h1,h3,rfl⟩,
    hf.trans (by
      have hi : allMass w s.T ≤1 := (pr_le_tot hw.nz).trans hw.total.le
      exact (mul_le_mul_of_nonneg_right hi (bp_pos _).le).trans_eq (one_mul _))⟩

end ImageLeafMixture
end
end Lax793645Proofs.Simplifications
