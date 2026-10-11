import Lax342547.MatchingSamples
import Mathlib.Data.Fintype.EquivFin

namespace Lax342547Proofs.MatchingSamples
open Lax342547.MatchingSamples

set_option backward.isDefEq.respectTransparency false
open Lax342547.ConnectedMatching Lax342547.SampledGraph

/--
---
conclusion: Lax342547.MatchingSamples.oriented_mem
---
-/
theorem oriented_mem {V : Type} (e : Finset V) (he : e.card = 2) (b : Bool) : oriented e he b ∈ e := by
  exact ((e.equivFinOfCardEq he).symm (if b then 1 else 0)).property

/--
---
conclusion: Lax342547.MatchingSamples.oriented_injective
---
-/
theorem oriented_injective {V : Type} (e : Finset V) (he : e.card = 2) : Function.Injective (oriented e he) := by
  intro b c h
  have hsub := Subtype.ext h
  have hh := (e.equivFinOfCardEq he).symm.injective hsub
  cases b <;> cases c <;> simp_all

/--
---
conclusion: Lax342547.MatchingSamples.oriented_covers
---
-/
theorem oriented_covers {V : Type} (e : Finset V) (he : e.card = 2) (v : V) (hv : v ∈ e) :
    ∃ b, oriented e he b = v := by
  let i := e.equivFinOfCardEq he ⟨v,hv⟩
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with hi|hi
  · refine ⟨false,?_⟩
    have hh := (e.equivFinOfCardEq he).symm_apply_apply ⟨v,hv⟩
    rw [show e.equivFinOfCardEq he ⟨v,hv⟩ = 0 from hi] at hh
    exact congrArg Subtype.val hh
  · refine ⟨true,?_⟩
    have hh := (e.equivFinOfCardEq he).symm_apply_apply ⟨v,hv⟩
    rw [show e.equivFinOfCardEq he ⟨v,hv⟩ = 1 from hi] at hh
    exact congrArg Subtype.val hh

/--
---
conclusion: Lax342547.MatchingSamples.matching_orientation_injective
---
-/
theorem matching_orientation_injective {V : Type} (G : SimpleGraph V) (M : Finset (Finset V))
    (hM : IsTouchingMatching G M) :
    Function.Injective (fun eb : M × Bool => oriented eb.1.val (hM.1 _ eb.1.property).1 eb.2) := by
  intro a b h
  change oriented a.1.val (hM.1 _ a.1.property).1 a.2 =
    oriented b.1.val (hM.1 _ b.1.property).1 b.2 at h
  have ha := Lax342547.MatchingSamples.oriented_mem a.1.val (hM.1 _ a.1.property).1 a.2
  have hb := Lax342547.MatchingSamples.oriented_mem b.1.val (hM.1 _ b.1.property).1 b.2
  have he : a.1 = b.1 := by
    apply Subtype.ext
    by_contra hn
    have hd := hM.2.1 _ a.1.property _ b.1.property hn
    have hbad := Finset.disjoint_left.mp hd ha
    exact hbad (h.symm ▸ hb)
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  dsimp at he
  subst b
  have hij := Lax342547.MatchingSamples.oriented_injective a.val (hM.1 _ a.property).1 h
  exact Prod.ext rfl hij

/--
---
conclusion: Lax342547.MatchingSamples.matching_unit_independence
---
-/
theorem matching_unit_independence {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) :
    ∀ e f : M, ¬ (∀ i j : Bool,
      hole (sample (oriented e.val (hM.1 _ e.property).1 i))
        (sample (oriented f.val (hM.1 _ f.property).1 j))) := by
  intro e f hholes
  by_cases hef : e = f
  · subst f
    exact hloop _ (hholes false false)
  · have hv : e.val ≠ f.val := by intro hh; exact hef (Subtype.ext hh)
    obtain ⟨v,hve,w,hwf,hadj⟩ := hM.2.2 _ e.property _ f.property hv
    obtain ⟨i,rfl⟩ := Lax342547.MatchingSamples.oriented_covers e.val (hM.1 _ e.property).1 v hve
    obtain ⟨j,rfl⟩ := Lax342547.MatchingSamples.oriented_covers f.val (hM.1 _ f.property).1 w hwf
    exact hadj.2 (hholes i j)


/--
---
conclusion: Lax342547.MatchingSamples.matching_unit_is_unit
---
-/
theorem matching_unit_is_unit {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) (e : M) :
    ¬ hole (unitType sample e.val (hM.1 _ e.property).1).1
      (unitType sample e.val (hM.1 _ e.property).1).2 := by
  have hne : oriented e.val (hM.1 _ e.property).1 false ≠ oriented e.val (hM.1 _ e.property).1 true := by
    intro h
    have hh := Lax342547.MatchingSamples.oriented_injective e.val (hM.1 _ e.property).1 h
    cases hh
  have hadj := (hM.1 _ e.property).2 (Lax342547.MatchingSamples.oriented_mem e.val _ false) (Lax342547.MatchingSamples.oriented_mem e.val _ true) hne
  exact hadj.2

/--
---
conclusion: Lax342547.MatchingSamples.unit_types_independent
---
-/
theorem unit_types_independent {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) : by
      classical
      exact let I := Finset.univ.image (fun e : M => unitType sample e.val (hM.1 _ e.property).1)
        (∀ u ∈ I, ¬ hole u.1 u.2) ∧ (∀ u ∈ I, ∀ v ∈ I, ¬ fourConflict hole u v) := by
  classical
  constructor
  · intro u hu
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    exact Lax342547.MatchingSamples.matching_unit_is_unit hole hsymm sample M hM e
  · intro u hu v hv hconf
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hv
    apply Lax342547.MatchingSamples.matching_unit_independence hole hsymm hloop sample M hM e f
    intro i j
    cases i <;> cases j
    · exact hconf.1
    · exact hconf.2.1
    · exact hconf.2.2.1
    · exact hconf.2.2.2

end Lax342547Proofs.MatchingSamples

