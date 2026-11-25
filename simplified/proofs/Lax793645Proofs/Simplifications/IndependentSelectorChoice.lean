import Lax793645Proofs.Simplifications.AffineSelectorExclusions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

variable {b j : ℕ}

theorem quotient_span_preimage {S : Type} [Fintype S]
    (U : Space (Vec S)) (A : Set (Vec S)) (x : Vec S)
    (hx : U.mkQ x ∈ Submodule.span F (U.mkQ '' A)) :
    x ∈ U ⊔ Submodule.span F A := by
  rw [←Submodule.map_span] at hx
  obtain ⟨y,hy,he⟩ := hx
  have hd : x-y ∈ U := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change U.mkQ (x-y)=0
    rw [map_sub,he,sub_self]
  exact Submodule.mem_sup.mpr ⟨x-y,hd,y,hy,sub_add_cancel x y⟩

/-- Greedy choices avoid a protected space and the span of all previous
selectors. Each allowed label set only needs more than the fixed closure
budget, independently of the eventual input dimension. -/
theorem independent_selector_fin_choice (hj : 1 ≤ j)
    (U : Space (Vec (SelIdx b j))) (k : ℕ) (A : Fin k → Finset (Label b))
    (hA : ∀ i,2^(dim U+k) < (A i).card) :
    ∃ s : Fin k → Label b, (∀ i,s i ∈ A i) ∧
      LinearIndependent F (U.mkQ ∘ (fun i => selV j (s i))) := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => i.elim0,linearIndependent_empty_type⟩
  | succ k ih =>
    have hsmall (i : Fin k) : 2^(dim U+k) < (A i.castSucc).card :=
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)).trans_lt (hA i.castSucc)
    obtain ⟨s,hs,hind⟩ := ih (fun i => A i.castSucc) hsmall
    let L := Finset.univ.image s
    let D := U ⊔ Submodule.span F (selV j '' (L : Set (Label b)))
    have hL : L.card ≤ k := by simpa [L] using Finset.card_image_le (f:=s) (s:=Finset.univ)
    have hcard : (selectorExcluded D).card < (A (Fin.last k)).card :=
      (selector_span_excluded_card hj U L).trans_lt
        ((Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)).trans_lt (hA _))
    obtain ⟨a,ha,he⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hnot : U.mkQ (selV j a) ∉
        Submodule.span F (Set.range (U.mkQ ∘ (fun i => selV j (s i)))) := by
      intro h
      apply he
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      apply quotient_span_preimage U _ _
      apply Submodule.span_mono _ h
      rintro _ ⟨i,rfl⟩
      exact ⟨selV j (s i),⟨s i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,rfl⟩,rfl⟩
    let s' : Fin (k+1) → Label b := Fin.snoc s a
    refine ⟨s',?_,?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa [s'] using ha
      | cast i => simpa [s'] using hs i
    have heq : (U.mkQ ∘ (fun i => selV j (s' i)))=
        Fin.snoc (U.mkQ ∘ (fun i => selV j (s i))) (U.mkQ (selV j a)) := by
      funext i
      induction i using Fin.lastCases with
      | last => simp [s',Function.comp_apply]
      | cast i => simp [s',Function.comp_apply]
    rw [heq]
    exact hind.finSnoc hnot

theorem independent_selector_choice {I : Type} [Fintype I]
    (hj : 1 ≤ j) (U : Space (Vec (SelIdx b j))) (A : I → Finset (Label b))
    (hA : ∀ i,2^(dim U+Fintype.card I) < (A i).card) :
    ∃ s : I → Label b, (∀ i,s i ∈ A i) ∧
      LinearIndependent F (U.mkQ ∘ (fun i => selV j (s i))) := by
  classical
  let e := Fintype.equivFin I
  obtain ⟨s,hs,hind⟩ := independent_selector_fin_choice hj U (Fintype.card I)
    (fun i => A (e.symm i)) (fun i => hA _)
  refine ⟨s ∘ e,fun i => by simpa using hs (e i),?_⟩
  exact hind.comp e e.injective

end
end Lax793645Proofs.Simplifications
