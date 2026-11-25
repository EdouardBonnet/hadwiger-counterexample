/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.LabeledGenerators.
Changes: require independence modulo protected spaces, using span avoidance
when choosing each new generator, in place of distinct addresses.
-/
import Lax793645Proofs.Simplifications.IndependentSelectorChoice
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.LabeledGenerators

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace IndependentClub
variable {L I S X Y : Type} [DecidableEq L] [DecidableEq I] [Fintype S]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable (C : Club I X L) (U : Bool → Space (Vec S)) (v : Bool → I → Vec S)

def fresh (p : Finset I) (i : I) : Prop :=
  ∀ b, (U b).mkQ (v b i) ∉ Submodule.span F ((U b).mkQ ∘ v b '' (p : Set I))

def bundle (p : Finset I) (s : Straps L) : Prop :=
  (∀ i∈p,C.zone s i) ∧ ∀ b,LinearIndepOn F ((U b).mkQ ∘ v b) (p : Set I)

def length3 (s : Straps L) (π : X →ₗ[F] Y) (x : X) : Prop :=
  ∃ p : Finset I,bundle C U v p s ∧ p.card ≤ 3 ∧ C.contents p=x ∧ π x=0

def ration (s : Straps L) (π : X →ₗ[F] Y) : Space X :=
  Submodule.span F (length3 C U v s π)

def yieldFresh (s : Straps L) (π : X →ₗ[F] Y) : Prop :=
  ∀ p : Finset I,p.card ≤ 2 → ∀ y,∃ i,C.zone s i ∧ π (C.writes i)=y ∧ fresh U v p i

theorem fresh_mono {p q : Finset I} (h : p ⊆ q) {i : I} (hi : fresh U v q i) :
    fresh U v p i := by
  intro b hb
  apply hi b
  exact Submodule.span_mono (Set.image_mono h) hb

theorem fresh_notMem {p : Finset I} {i : I} (h : fresh U v p i) : i ∉ p := by
  intro hi
  exact h true (Submodule.subset_span ⟨i,hi,rfl⟩)

theorem bundle_one (s : Straps L) {i : I} (hi : C.zone s i)
    (hn : ∀ b,(U b).mkQ (v b i) ≠ 0) : bundle C U v {i} s := by
  refine ⟨fun j hj => (Finset.mem_singleton.mp hj).symm ▸ hi,fun b => ?_⟩
  simpa only [Finset.coe_singleton,linearIndepOn_singleton_iff,Function.comp_apply] using hn b

theorem bundle_insert (s : Straps L) {i : I} (hi : C.zone s i) (p : Finset I)
    (hp : bundle C U v p s) (hf : fresh U v p i) : bundle C U v (insert i p) s := by
  refine ⟨fun j hj => ?_,fun b => ?_⟩
  · rcases Finset.mem_insert.mp hj with rfl|hj
    · exact hi
    exact hp.1 j hj
  rw [Finset.coe_insert]
  exact (linearIndepOn_insert (fresh_notMem U v hf)).mpr ⟨hp.2 b,hf b⟩

theorem band_contents (s : Straps L) {p : Finset I} (hp : bundle C U v p s) :
    C.contents p ∈ C.band s :=
  Submodule.sum_mem _ (fun i hi => C.band_write s (hp.1 i hi))

theorem length3_zero (s : Straps L) (π : X →ₗ[F] Y) : length3 C U v s π 0 := by
  refine ⟨∅,⟨by simp,?_⟩,by simp,by simp [Club.contents],map_zero π⟩
  intro b
  simp

theorem ration_le (s : Straps L) (π : X →ₗ[F] Y) :
    ration C U v s π ≤ C.band s ⊓ LinearMap.ker π := by
  apply Submodule.span_le.mpr
  rintro x ⟨p,hp,_,rfl,hx⟩
  exact ⟨band_contents C U v s hp,hx⟩

set_option maxHeartbeats 900000 in
/-- Kernel relations are spanned by at most three generators whose selectors
are independent modulo the protected spaces on both sides. -/
theorem ration_eq (s : Straps L) (π : X →ₗ[F] Y)
    (hn : ∀ i,C.zone s i → ∀ b,(U b).mkQ (v b i) ≠ 0)
    (h : yieldFresh C U v s π) :
    ration C U v s π=C.band s ⊓ LinearMap.ker π := by
  classical
  let R := ration C U v s π
  let q := R.mkQ
  have hr (i j : I) (hi : C.zone s i) (hj : C.zone s j)
      (ht : π (C.writes i)=π (C.writes j)) (hf : fresh U v {j} i) :
      q (C.writes i)=q (C.writes j) := by
    have hij : i ≠ j := by intro he; subst i; exact fresh_notMem U v hf (by simp)
    apply add_right_cancel (b:=q (C.writes j))
    rw [char_two,←map_add]
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    refine Submodule.subset_span ⟨{i,j},bundle_insert C U v s hi _
      (bundle_one C U v s hj (hn j hj)) hf,by simp [hij],?_,?_⟩
    · simp [Club.contents,hij]
    rw [map_add,ht,char_two]
  let f := C.writes
  have hg (i j : I) (hi : C.zone s i) (hj : C.zone s j)
      (ht : π (f i)=π (f j)) : q (f i)=q (f j) := by
    obtain ⟨t,ht',hy,hf⟩ := h {i,j} (by by_cases he : i=j <;> simp [he]) (π (f j))
    exact (hr t i ht' hi (hy.trans ht.symm)
      (fresh_mono U v (by simp) hf)).symm.trans
        (hr t j ht' hj hy (fresh_mono U v (by simp) hf))
  choose g he hG hP using fun y => h ∅ (by simp) y
  let T (y : Y) := q (f (g y))
  have hq i (hi : C.zone s i) : T (π (f i))=q (f i) := hg _ i (he _) hi (hG _)
  have h0 : T 0=0 := by
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    exact Submodule.subset_span ⟨{g 0},bundle_one C U v s (he 0) (hn _ (he 0)),
      by simp,by simp [f,Club.contents],hG 0⟩
  have hadd (x y) : T (x+y)=T x+T y := by
    let i := g x
    obtain ⟨j,hj,hJ,hA⟩ := h {i} (by simp) y
    have hji : j ≠ i := by intro he; subst j; exact fresh_notMem U v hA (by simp)
    let t : Finset I := {j,i}
    have ht : t.card=2 := by simp [t,hji]
    obtain ⟨k,hk,hK,hB⟩ := h t (by omega) (x+y)
    have hkt : k ∉ t := fresh_notMem U v hB
    have hQ : q (f k)+(q (f j)+q (f i))=0 := by
      have hR : length3 C U v s π (f k+(f j+f i)) := by
        refine ⟨insert k t,bundle_insert C U v s hk _
          (bundle_insert C U v s hj _ (bundle_one C U v s (he x) (hn _ (he x))) hA) hB,
          ?_,?_,?_⟩
        · rw [Finset.card_insert_of_notMem hkt,ht]
        · rw [Club.contents,Finset.sum_insert hkt]
          simp [t,f,hji]
        rw [map_add,map_add,hK,hJ,hG,add_comm y,char_two]
      rw [←map_add,←map_add]
      exact (Submodule.Quotient.mk_eq_zero R).mpr (Submodule.subset_span hR)
    have hq' (z a) (hz : C.zone s a) (ha : π (C.writes a)=z) : q (f a)=T z := by
      rw [←ha]; exact (hq a hz).symm
    rw [hq' _ k hk hK,hq' _ j hj hJ,hq' x i (he x) (hG x),add_comm (T y)] at hQ
    exact add_right_cancel (hQ.trans (char_two _).symm)
  apply le_antisymm (ration_le C U v s π)
  rintro x ⟨hy,hx⟩
  apply (Submodule.Quotient.mk_eq_zero R).mp
  have hz {x} (hx : x ∈ C.band s) : q x=T (π x) := by
    induction hx using Submodule.span_induction with
    | zero => rw [map_zero,map_zero,h0]
    | mem x hx => obtain ⟨i,hi,rfl⟩ := hx; exact (hq i hi).symm
    | add a b _ _ ha hb => rw [map_add,map_add,hadd,ha,hb]
    | smul a b _ hb =>
      rcases bit_cases a with ha|ha
      · rw [ha,zero_smul,map_zero,map_zero,h0]
      rw [ha,one_smul,hb]
  change q x=0
  change π x=0 at hx
  rw [hz hy,hx,h0]

end IndependentClub
end
end Lax793645Proofs.Simplifications
