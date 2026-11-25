import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProductLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SampledGraphs
import Mathlib.Data.Fintype.Powerset

namespace Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
open Finset Real HadwigerMatching
open scoped BigOperators
variable {A V : Type*}

/-- k distinct samples in S (unordered). -/
def badS (S : A → Prop) (k : ℕ) (x : V → A) :=
  ∃ T : Finset V, T.card = k ∧ ∀ v ∈ T, S (x v)

theorem badS_pr [Fintype A] {μ : Wgt A} (hμ : IsLaw μ)
    (S : A → Prop) (k m : ℕ) :
    pr (prodW (fun _ : Fin m => μ)) (badS S k) ≤
      2 ^ m * (pr μ S)^k := by
  classical
  let q := prodW (fun _ : Fin m => μ)
  have hp (T : Finset (Fin m)) :
      pr q (fun x => T.card = k ∧ ∀ v ∈ T, S (x v)) ≤ (pr μ S)^k := by
    by_cases h : T.card = k
    · have e (x : Fin m → A) : (∀ v ∈ T, S (x v)) ↔ ∀ v : T, S (x v.val) := by simp
      have h' := prodW_pr_inj (e:=fun v : T => v.val) Subtype.val_injective
        (w:=fun _ => μ) (fun _ => hμ) (fun _ : T => S)
      simp_rw [h, true_and, e]
      simp only [prod_const, Finset.card_univ, Fintype.card_coe,h] at h'
      exact h'.le
    · have hn : 0 ≤ pr μ S := pr_nonneg hμ.nz
      simp only [h, false_and, pr_false]
      positivity
  have he := pr_exists_le (prodW_nonneg (w:=fun _ : Fin m => μ) (fun _ => hμ.nz))
    (fun T : Finset (Fin m) => (fun x => T.card = k ∧ ∀ v ∈ T, S (x v)))
  refine he.trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
  simp

/-- k pair exceptions using disjoint sample positions (ordered pairs). -/
def badE (E : A × A → Prop) (k : ℕ) (x : V → A) :=
  ∃ e : Fin k ⊕ Fin k → V, Function.Injective e ∧
    ∀ i, E (x (e (.inl i)), x (e (.inr i)))

theorem badE_pr [Fintype A] {μ : Wgt A} (hμ : IsLaw μ)
    (E : A × A → Prop) (k m : ℕ) :
    pr (prodW (fun _ : Fin m => μ)) (badE E k) ≤
      (m : ℝ)^(k+k) * (pr (pairW μ μ) E)^k := by
  classical
  let Q := prodW (fun _ : Fin m => μ)
  let P (e : Fin k ⊕ Fin k → Fin m) (x : Fin m → A) :=
    Function.Injective e ∧ ∀ i, E (x (e (.inl i)), x (e (.inr i)))
  have hp (e : Fin k ⊕ Fin k → Fin m) :
      pr Q (P e) ≤ (pr (pairW μ μ) E)^k := by
    by_cases h : Function.Injective e
    · have h' := prodW_map_pairs e h hμ
      let f (x : Fin m → A) (i : Fin k) := (x (e (.inl i)), x (e (.inr i)))
      have hp : P e = (fun x => ∀ i, E (f x i)) := by simp [P,h,f]
      rw [hp, ← mapW_pr Q f (fun x => ∀ i, E (x i))]
      change mapW Q f = _ at h'
      rw [h']
      have hb := prodW_pr (w:=fun _ : Fin k => pairW μ μ) (p:=fun _ => E)
      simpa using hb.le
    · have hn : 0 ≤ pr (pairW μ μ) E := pr_nonneg (pairW_law hμ hμ).nz
      simp only [P,h,false_and,pr_false]; positivity
  have he := pr_exists_le (prodW_nonneg (w:=fun _ : Fin m => μ) (fun _ => hμ.nz)) P
  refine he.trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
  simp

theorem many_bad {x : V → A} (S : A → Prop) (E : A × A → Prop)
    {k t : ℕ} (ht : k + k ≤ t + 1)
    {e : Fin t ⊕ Fin t → V} (he : Function.Injective e)
    (hp : ∀ i, S (x (e (.inl i))) ∨ S (x (e (.inr i))) ∨
      E (x (e (.inl i)), x (e (.inr i)))) :
    badS S k x ∨ badE E k x := by
  classical
  let p (i : Fin t) := S (x (e (.inl i))) ∨ S (x (e (.inr i)))
  let I := univ.filter p
  let J := univ.filter (fun i => ¬ p i)
  by_cases hI : k ≤ I.card
  · left
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card I by simpa using hI)
    let f : Fin k → Fin t := fun i => r i
    have hf : Function.Injective f := fun i j g => r.injective (Subtype.ext g)
    let y : Fin k → Fin t ⊕ Fin t :=
      fun i => if S (x (e (.inl (f i)))) then .inl (f i) else .inr (f i)
    have hy (i : Fin k) : S (x (e (y i))) := by
      have h : p (f i) := (mem_filter.mp (r i).property).2
      unfold p at h
      unfold y
      split
      · assumption
      · rename_i hn; exact h.resolve_left hn
    have hid i : Sum.elim id id (y i) = f i := by unfold y; split <;> rfl
    have hy' : Function.Injective y := fun i j g =>
      hf (by rw [←hid,←hid,g])
    refine ⟨univ.image (e ∘ y), by rw [card_image_of_injective _ (he.comp hy')]; simp,?_⟩
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact hy i
  · right
    have hJ : k ≤ J.card := by
      have hsum : I.card + J.card = t := by
        simpa using Finset.card_filter_add_card_filter_not (s:=univ) p
      omega
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card J by simpa using hJ)
    let f : Fin k → Fin t := fun i => r i
    have hf : Function.Injective f := fun i j g => r.injective (Subtype.ext g)
    refine ⟨e ∘ Sum.map f f, he.comp (Sum.map_injective.mpr ⟨hf,hf⟩),?_⟩
    intro i
    have h : ¬p (f i) := (mem_filter.mp (r i).property).2
    exact ((hp _).resolve_left (fun g => h (Or.inl g))).resolve_left
      (fun g => h (Or.inr g))

end
end Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
