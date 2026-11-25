import Lax793645Proofs.Simplifications.AuxiliaryMomentBudget

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Direct even moments beat every fixed exponential density cap. The
nominal phase is arbitrary but is fixed before the orientation is drawn. -/
theorem one_direct_moment_decay {I : Type} [Fintype I] [DecidableEq I]
    {p : Shape} (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) :
    ∃ s : ℕ,0<s ∧ ∀ H : ℝ,0≤H→∃ δ : ℝ,0<δ ∧
      ∀ᶠ n : ℕ in atTop,0<2*(n/(2*s)) ∧
      ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n→
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (ψ : Wgt (Inputs p n I)),
      (∀ x,|D x|≤1)→(∀ x,D x≠0 → oneOwnPart v.t q x)→
      (∀ ξ,|linearFourier D ξ|≤δ)→(∀ x,|ψ x|≤1)→
      avg (oneUnitRaw mixer (M*n))
        (fun o=>|oneQueryCorrelation v D ψ o|^(2*(n/(2*s))))≤bp (-H*n) := by
  let J:=KeySlots p v.t
  let k:=num J
  have hk : 0≤k:=Nat.cast_nonneg _
  obtain ⟨s,hs,hcal⟩:=auxiliary_even_budget_calendar J (Ports p) M hM (num I) k (Nat.cast_nonneg _) hk
  refine ⟨s,hs,fun H hH=>?_⟩
  obtain ⟨a,t,δ,hδ,hcal⟩:=hcal H hH
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal] with n hn
  obtain ⟨hl,hr,ht,hbudget⟩:=hn
  refine ⟨hl,fun mixer hN q D ψ hD hsup hF hψ=>?_⟩
  let l:=2*(n/(2*s))
  have hslots e : num (Port (directQueryRoute v (Fin l)) e)≤k*l:=by
    have hh:=port_limit (directQueryRoute v (Fin l)) e
    simpa only [num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,k,J,mul_comm] using hh
  have hraw:=one_auxiliary_query_moment (T:=Fin l) v mixer hN q D δ hδ.le
    hD hsup hF ψ hψ (k*l) (mul_nonneg hk (Nat.cast_nonneg _)) hslots hr a t ht
  have htail : bp ((num (Fin l)*num I-n)*a)≤bp ((3*(l:ℝ)*num I-n)*a):=by
    apply bp_le
    simp only [num,Fintype.card_fin]
    nlinarith [(Nat.cast_nonneg l : (0:ℝ)≤l),(Nat.cast_nonneg a : (0:ℝ)≤a),
      mul_nonneg (Nat.cast_nonneg l : (0:ℝ)≤l) (Nat.cast_nonneg (Fintype.card I))]
  have he : Even l:=even_two_mul _
  change avg (oneUnitRaw mixer (M*n)) (fun o=>|oneQueryCorrelation v D ψ o|^l)≤_
  simp_rw [he.pow_abs]
  exact (le_abs_self _).trans (by
    simpa only [Fintype.card_fin] using hraw.trans ((add_le_add le_rfl htail).trans hbudget))

end
end Lax793645Proofs.Simplifications
