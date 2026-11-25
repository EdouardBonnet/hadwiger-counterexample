import Lax793645Proofs.Simplifications.ColoredCutEnergy
import Lax793645Proofs.Simplifications.GramReferenceBias
import Lax793645Proofs.Simplifications.QueryDensityRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {O X B C : Type} [Fintype O] [Fintype X] [Fintype B] [Nonempty B] [Fintype C]

theorem conditional_cell_mass (S : B→Prop) (hS : 0<pr unif S) (P : B→C) (c : C) :
    pr unif (fun x=>S x ∧ P x=c)=pr unif S*mapW (unifOn S) P c := by
  change pr unif (fun x=>S x ∧ P x=c)=pr unif S*avg (unifOn S) (fun x=>ind (P x=c))
  rw [←part_reset S (fun x=>ind (P x=c)) hS]
  unfold pr partMean
  simp only [ind_and]

/-- A repeated-hit tail on ambient sets controls every positive cell of
a conditional reference law. Empty cells cost nothing. -/
theorem conditional_cell_hits (π : Wgt O) (hπ : IsLaw π) (κ : Wgt X)
    (K : O→X→B) (S : B→Prop) (P : B→C)
    (B₀ τ δ ρ η : ℝ) (hB : 0≤B₀) (hτ : 0<τ) (hδ : 0<δ) (hη : 0≤η)
    (hmass : τ≤pr unif S) (hsmall : ρ≤τ*δ)
    (hs : stamina (mapW (unifOn S) P) δ)
    (ht : ∀ A : B→Prop,ρ≤pr unif A →
      pr π (fun o=>B₀*pr unif A<pr (mapW κ (K o)) A)≤η) :
    ∀ c,pr π (fun o=>B₀*mapW (unifOn S) P c<
      pr (mapW κ (K o)) (fun x=>S x ∧ P x=c))≤η := by
  intro c
  have hS : 0<pr unif S:=hτ.trans_le hmass
  have he:=conditional_cell_mass S hS P c
  by_cases hc : mapW (unifOn S) P c=0
  · have hfalse : (fun x=>S x ∧ P x=c)=(fun _=>False) := by
      funext x
      apply propext
      refine ⟨fun hx=>?_,fun h=>h.elim⟩
      have hh:=weight_le_pr (p:=fun x=>S x ∧ P x=c) (unif_law (α:=B)).nz hx
      rw [he,hc,mul_zero] at hh
      have hp : 0<(unif : Wgt B) x := by rw [unif_apply]; positivity
      exact (not_lt_of_ge hh) hp
    simp only [hfalse,pr_false,hc,mul_zero,lt_self_iff_false]
    exact hη
  · have hδc:=hs c hc
    have hA : ρ≤pr unif (fun x=>S x ∧ P x=c) := by
      rw [he]
      exact hsmall.trans (mul_le_mul hmass hδc hδ.le (pr_nonneg unif_law.nz))
    refine (pr_mono hπ.nz (fun o ho=>?_)).trans (ht _ hA)
    have hm : pr unif S≤1:=by exact (pr_le_tot unif_law.nz).trans_eq unif_law.total
    obtain ⟨x,hx,_⟩:=exists_of_pr_pos unif_law.nz hS
    have hn : 0≤mapW (unifOn S) P c:=map_nz (unifOn_law ⟨x,hx⟩).nz P c
    have hh : pr unif (fun x=>S x ∧ P x=c)≤mapW (unifOn S) P c := by
      rw [he]
      exact (mul_le_mul_of_nonneg_right hm hn).trans_eq (one_mul _)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh hB) ho

end
end Lax793645Proofs.Simplifications
