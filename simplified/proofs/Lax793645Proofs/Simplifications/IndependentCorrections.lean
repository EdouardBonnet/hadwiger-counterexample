/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.FreshGeneratorCorrection.
Changes: preserve independence modulo protected selector spaces, rather than
only distinctness of labels, when combining the two short corrections.
-/
import Lax793645Proofs.Simplifications.IndependentGenerators

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace IndependentClub
variable {L I S X Y : Type} [DecidableEq L] [DecidableEq I] [Fintype S]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable (C : Club I X L) (U : Bool → Space (Vec S)) (v : Bool → I → Vec S)

def enlarge (p : Finset I) (b : Bool) : Space (Vec S) :=
  U b ⊔ Submodule.span F (v b '' (p : Set I))

theorem enlarge_empty : enlarge U v ∅=U := by
  funext b
  simp [enlarge]

theorem enlarge_union (p q : Finset I) :
    enlarge (enlarge U v p) v q=enlarge U v (p∪q) := by
  funext b
  simp only [enlarge,Finset.coe_union,Set.image_union,Submodule.span_union,sup_assoc]

theorem bundle_weaken {U' : Bool → Space (Vec S)} (hU : ∀ b,U b ≤ U' b)
    {s : Straps L} {p : Finset I} (hp : bundle C U' v p s) : bundle C U v p s := by
  refine ⟨hp.1,fun b => ?_⟩
  let f := (U b).mapQ (U' b) LinearMap.id (hU b)
  have he : LinearIndependent F (f ∘ (fun i : (p : Set I) => (U b).mkQ (v b i.val))) := by
    simpa only [f,LinearIndepOn,Function.comp_def,Submodule.mkQ_apply,
      Submodule.mapQ_apply,LinearMap.id_apply] using hp.2 b
  exact he.of_comp f

theorem bundle_combine {p q : Finset I} {s : Straps L}
    (hp : bundle C U v p s) (hq : bundle C (enlarge U v p) v q s) :
    bundle C U v (p∪q) s ∧ Disjoint p q := by
  classical
  have hmono (b) : U b ≤ enlarge U v p b := le_sup_left
  have hpIn (b) (i : I) (hi : i∈p) : v b i ∈ enlarge U v p b :=
    Submodule.mem_sup_right (Submodule.subset_span ⟨i,hi,rfl⟩)
  have hdis : Disjoint p q := by
    apply Finset.disjoint_left.mpr
    intro i hi hq'
    have he := (hq.2 true).ne_zero hq'
    exact he ((Submodule.Quotient.mk_eq_zero _).mpr (hpIn true i hi))
  refine ⟨⟨fun i hi => ?_,fun b => ?_⟩,hdis⟩
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact hp.1 i hi
    exact hq.1 i hi
  let f := (U b).mapQ (enlarge U v p b) LinearMap.id (hmono b)
  have he : LinearIndependent F (f ∘ (fun i : (q : Set I) => (U b).mkQ (v b i.val))) := by
    simpa only [f,LinearIndepOn,Function.comp_def,Submodule.mkQ_apply,
      Submodule.mapQ_apply,LinearMap.id_apply] using hq.2 b
  have hr : Set.range (fun i : (q : Set I) => (U b).mkQ (v b i.val))=
      (U b).mkQ ∘ v b '' (q : Set I) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
    rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  have hd := Submodule.range_ker_disjoint he
  rw [hr] at hd
  have hker : Submodule.span F ((U b).mkQ ∘ v b '' (p : Set I)) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change (enlarge U v p b).mkQ (v b i)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hpIn b i hi)
  rw [Finset.coe_union]
  exact (hp.2 b).union (he.of_comp f) (hd.symm.mono_left hker)

private theorem binary_word {x z : X} (h : z ∈ Submodule.span F {x}) : z=0 ∨ z=x := by
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h
  rcases bit_cases a with h|h
  · left; simpa [h] using ha.symm
  right; simpa [h] using ha.symm

variable [Module.Finite F X]

set_option maxHeartbeats 1000000 in
/-- Two independent short kernel corrections suffice in a two-dimensional
kernel, provided its span survives protection of the first three choices. -/
theorem jump_two (s : Straps L) (π : X →ₗ[F] Y) (R : Space X)
    (hspan : ∀ p : Finset I,p.card ≤ 3 → ration C (enlarge U v p) v s π=R)
    (hdim : dim R ≤ 2) (x : X) (hx : x∈R) :
    ∃ p : Finset I,bundle C U v p s ∧ p.card ≤ 6 ∧ C.contents p=x := by
  classical
  by_cases h0 : x=0
  · obtain ⟨p,hp,hc,hs,_⟩ := length3_zero C U v s π
    exact ⟨p,hp,hc.trans (by decide),hs.trans h0.symm⟩
  have hex (p : Finset I) (hp : p.card ≤ 3) (Q : Space X) (hQ : x∉Q) :
      ∃ y,y∈R ∧ length3 C (enlarge U v p) v s π y ∧ y∉Q := by
    have hx' : x ∈ ration C (enlarge U v p) v s π := (hspan p hp).symm ▸ hx
    by_contra! hn
    exact hQ ((Submodule.span_le.mpr (fun y hy =>
      hn y ((hspan p hp) ▸ Submodule.subset_span hy) hy)) hx')
  obtain ⟨y,hy,⟨p,hp,hP,hY,_⟩,hny⟩ := hex ∅ (by simp) ⊥ (by simpa using h0)
  rw [enlarge_empty] at hp
  have hy0 : y≠0 := by simpa using hny
  let A := Submodule.span F {y}
  by_cases hA : x∈A
  · exact ⟨p,hp,hP.trans (by decide),hY.trans (((binary_word hA).resolve_left h0).symm)⟩
  obtain ⟨z,hz,⟨q,hq,hQ,hZ,_⟩,hnz⟩ := hex p hP A hA
  let B := Submodule.span F {z}
  have hab : A ⊔ B=R := by
    have hle : A ⊔ B ≤ R := sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr hy)
      ((Submodule.span_singleton_le_iff_mem ..).mpr hz)
    have hr := Submodule.finrank_sup_span_singleton hnz
    have ha : dim A=1 := finrank_span_singleton hy0
    apply Submodule.eq_of_le_of_finrank_le hle
    change dim R ≤ dim (A ⊔ B : Space X)
    change dim (A ⊔ B : Space X)=dim A+1 at hr
    rw [hr,ha]
    exact hdim
  obtain ⟨u,hu,t,ht,he⟩ := Submodule.mem_sup.mp (hab.symm ▸ hx)
  rcases binary_word hu with hu|hu <;> rcases binary_word ht with ht|ht
  · rw [hu,ht,zero_add] at he; exact (h0 he.symm).elim
  · rw [hu,ht,zero_add] at he
    exact ⟨q,bundle_weaken C U v (fun _ => le_sup_left) hq,hQ.trans (by decide),hZ.trans he⟩
  · rw [hu,ht,add_zero] at he
    exact ⟨p,hp,hP.trans (by decide),hY.trans he⟩
  obtain ⟨hfull,hdis⟩ := bundle_combine C U v hp hq
  refine ⟨p∪q,hfull,(Finset.card_union_le ..).trans (by omega),?_⟩
  rw [Club.contents,Finset.sum_union hdis]
  change C.contents p+C.contents q=x
  rw [hY,hZ,←hu,←ht]
  exact he

end IndependentClub
end
end Lax793645Proofs.Simplifications
