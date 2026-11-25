import Lax793645Proofs.Simplifications.AffineQueryHistograms

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Filter Function Matrix Finset
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {side : Bool}

def accounting (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q → F) (m : Mixer p n) (s : Charts p n d)
    (μ : Wgt (UnitType p n N)) (pin : Pin p n N) (K r : ℕ) (δ R ε η : ℝ) :=
  let Q := custom w μ s t z m pin K
  let ν := lawNu p N t z
  (∀ i,Q i → SubLaw i ∧ lsupp i ν) ∧ roster Q r ε ∧ smallSet Q ν δ η ∧ rosterTail Q ν R η

set_option maxHeartbeats 900000 in
/-- Uniform histogram control for the accepted densities, including all
orientation filters. The pin and its good-input flag are chosen after the
constants, and the finite net for each leaf is chosen before the opposite leaf. -/
theorem ownCertificate (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q → F) (M : ℕ) (hM : 1 ≤ M) (hr : 1 ≤ p.r)
    (C : ℝ) (hC : 0 ≤ C) (hw : w.moral t z)
    (ε η : ℝ) (he : 0 < ε) (hη : 0 < η) :
    ∃ (r : ℕ) (δ R : ℝ),0 < δ ∧ 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n
      ∀ (m : Mixer p n) (s : Charts p n d) (μ : Wgt (UnitType p n N))
        (pin : Pin p n N) (K : ℕ),
        2*num (Full p n) < (N : ℝ) → IsLaw μ →
        (∀ i,μ i ≤ bp (C*N)*PreparationParameters.usual p m N i) →
        accounting w t z m s μ pin K r δ R ε η := by
  classical
  let v := w.pen t
  obtain ⟨r,δ,R,hd,hR,hV⟩ := v.controls M hM Bool C η ε hC hη he
  refine ⟨r,δ,R,hd,hR,?_⟩
  filter_upwards [hV,eventually_ge_atTop (2*p.r)] with n hn hage N m s μ pin K hN hμ hv
  let u := w.policies t z n
  have hu i : IsLaw (u i) := Appearance.witLaw (w.allure_apt t z hw i) hr hage
  have ha := hn m hN μ hμ hv u hu (fun i => scopedZ_bit p n _ _ _ (hu _))
    (billboard w s t z m pin K)
  let P := ownPart (p:=p) (N:=N) t z
  obtain ⟨hh,_,_,hQ⟩ := ha
  have hrest : roster (custom w μ s t z m pin K) r ε ∧
      smallSet (custom w μ s t z m pin K) (lawNu p N t z) δ η ∧
      rosterTail (custom w μ s t z m pin K) (lawNu p N t z) R η := hQ P
  refine ⟨fun i hi => ?_,hrest⟩
  obtain ⟨x,hp,rfl⟩ := hi
  refine ⟨subLaw_sub (hh x hp) P,fun i hi => ?_⟩
  have ht := density_hung P (subW x P) (subW_carried x P) i
  exact left_ne_zero_of_mul (ht.symm ▸ hi)

end AffineOptions
end
end Lax793645Proofs.Simplifications
