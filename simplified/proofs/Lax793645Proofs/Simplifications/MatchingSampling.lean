import Lax793645Proofs.Simplifications.MatchingFilters
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteSampling

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section
variable {A V X I : Type*} [Fintype A]

theorem unif_event_card [Fintype X] (P : X → Prop) [DecidablePred P] :
    pr (unif : Wgt X) P = ((Finset.univ.filter P).card:ℝ)/Fintype.card X := by
  classical
  simp [pr,avg,unif_apply,ind,div_eq_mul_inv,Finset.sum_ite]

theorem map_carried [Fintype I] (w : Wgt I) (f : I → X) (P : X → Prop)
    (h : ∀ i, P (f i)) : carried (mapW w f) P := by
  intro x hx
  change avg w (fun i => ind (f i=x))=0
  have hi i : f i ≠ x := fun he => hx (he ▸ h i)
  simp only [ind_zero (hi _),avg_zero]

theorem map_nonconflict [Fintype I] (w : Wgt I) (f : I → X) (C : X → X → Prop)
    (h : ∀ i j, ¬C (f i) (f j)) (y x : X) (hc : C y x) :
    mapW w f y*mapW w f x=0 := by
  by_cases hy : ∃ i, f i=y
  · obtain ⟨i,rfl⟩ := hy
    have hx : ∀ j, f j ≠ x := fun j he => h i j (he.symm ▸ hc)
    have hz : mapW w f x=0 := by
      change avg w (fun j => ind (f j=x))=0
      simp only [ind_zero (hx _),avg_zero]
    rw [hz,mul_zero]
  · have hz : mapW w f y=0 := by
      change avg w (fun i => ind (f i=y))=0
      have hi i : f i ≠ y := fun he => hy ⟨i,he⟩
      simp only [ind_zero (hi _),avg_zero]
    rw [hz,zero_mul]

/-- A good raw sample leaves at least half of the matching edges usable, for
every history simultaneously. Repeated sampling from the matching is allowed. -/
theorem matching_retained_mass {k s : ℕ} (hk : 0 < k) (hs : 4*s ≤ k)
    (x : V → A) (e : Fin k ⊕ Fin k → V) (he : Function.Injective e)
    (S : A → Prop) (E : A × A → Prop)
    (hgood : ¬(badS S s x ∨ badE E s x)) :
    1/2 ≤ pr (mapW (unif : Wgt (Fin k))
      (fun i => (x (e (.inl i)),x (e (.inr i)))))
      (fun p => ¬S p.1 ∧ ¬S p.2 ∧ ¬E p) := by
  classical
  let f (i : Fin k) := (x (e (.inl i)),x (e (.inr i)))
  let P (i : Fin k) := ¬S (f i).1 ∧ ¬S (f i).2 ∧ ¬E (f i)
  let I := Finset.univ.filter (fun i => ¬P i)
  have hi : I.card+1 < 2*s := by
    by_contra! hn
    let t := I.card
    let eqv : I ≃ Fin t := Fintype.equivFinOfCardEq (by simp [t])
    let g : Fin t → Fin k := fun i => (eqv.symm i).val
    have hg : Function.Injective g := fun i j hij =>
      eqv.symm.injective (Subtype.ext hij)
    have hbad := many_bad S E (by omega : s+s ≤ t+1)
      (he.comp (Sum.map_injective.mpr ⟨hg,hg⟩)) (fun i : Fin t => by
        have hm : ¬P (g i) := (Finset.mem_filter.mp (eqv.symm i).property).2
        dsimp only [P,f] at hm
        push Not at hm
        change S (x (e (.inl (g i)))) ∨ S (x (e (.inr (g i)))) ∨ E (x (e (.inl (g i))),x (e (.inr (g i))))
        tauto)
    exact hgood hbad
  have hj : 2*(Finset.univ.filter P).card ≥ k := by
    have ht := Finset.card_filter_add_card_filter_not (s:=Finset.univ) P
    have hk' : (Finset.univ : Finset (Fin k)).card=k := by simp
    change (Finset.univ.filter P).card+I.card=(Finset.univ : Finset (Fin k)).card at ht
    omega
  rw [mapW_pr]
  change 1/2 ≤ pr (unif : Wgt (Fin k)) P
  rw [unif_event_card,Fintype.card_fin]
  apply (le_div_iff₀ (by exact_mod_cast hk : (0:ℝ)<k)).mpr
  have hj' : (k:ℝ) ≤ 2*((Finset.univ.filter P).card:ℝ) := by exact_mod_cast hj
  linarith

end
end Lax793645Proofs.Simplifications
