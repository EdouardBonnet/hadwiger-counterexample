import Lax793645Proofs.Simplifications.PredictedPlans

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
noncomputable section

theorem fresh_fin_choice {A : Type} [Fintype A] (k : ℕ) (S : Fin k → Finset A)
    (hS : ∀ i, k ≤ (S i).card) :
    ∃ f : Fin k → A, Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨f,hf,hmem⟩ := ih (fun i => S i.castSucc) (fun i => (Nat.le_succ k).trans (hS i.castSucc))
    have hcard : (univ.image f).card < (S (Fin.last k)).card := by
      have h1 := Finset.card_image_le (f:=f) (s:=univ)
      simp only [card_univ,Fintype.card_fin] at h1
      exact h1.trans_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (hS _))
    obtain ⟨a,ha,hfresh⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    let g : Fin (k+1) → A := Fin.lastCases a f
    refine ⟨g,?_,?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j =>
          have he : a=f j := by simpa [g] using hij
          exact False.elim (hfresh (he.symm ▸ mem_image_of_mem f (mem_univ j)))
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          have he : f i=a := by simpa [g] using hij
          exact False.elim (hfresh (he ▸ mem_image_of_mem f (mem_univ i)))
        | cast j => exact congrArg Fin.castSucc (hf (by simpa [g] using hij))
    · intro i
      induction i using Fin.lastCases with
      | last => simpa [g] using ha
      | cast i => simpa [g] using hmem i

theorem fresh_finite_choice {I A : Type} [Fintype I] [Fintype A]
    (S : I → Finset A) (hS : ∀ i, Fintype.card I ≤ (S i).card) :
    ∃ f : I → A, Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  let e := Fintype.equivFin I
  obtain ⟨f,hf,hm⟩ := fresh_fin_choice (Fintype.card I) (fun i => S (e.symm i)) (fun i => hS _)
  exact ⟨f ∘ e,hf.comp e.injective,fun i => by simpa using hm (e i)⟩

theorem predicted_labels {p : Shape} {q : Format} {n M s0 : ℕ}
    {b : PreparationParameters} (h : AnalyticParameters p M b s0)
    (plan : Plan p n) (H L : Stalls p) (hb : booths p b.pins plan H)
    (hL : ∀ i, (L i).card ≤ b.B) (hs : Fintype.card (Messenger q) ≤ 12) (side : Bool) :
    ∃ f : Messenger q → Label p.b, Injective f ∧
      ∀ i, f i ∉ H (parcel side i) ∧ f i ∉ L (parcel side i) := by
  classical
  let S (i : Messenger q) := (H (parcel side i) ∪ L (parcel side i))ᶜ
  have hS i : Fintype.card (Messenger q) ≤ (S i).card := by
    have hu := Finset.card_union_le (H (parcel side i)) (L (parcel side i))
    have hf := hb.1 (parcel side i)
    have hl := hL (parcel side i)
    have h1 := h.forbid
    have h2 := h.spare
    unfold S
    rw [Finset.card_compl]
    omega
  obtain ⟨f,hf,hm⟩ := fresh_finite_choice S hS
  exact ⟨f,hf,fun i => by simpa [S] using hm i⟩

end
end Lax793645Proofs.Simplifications
