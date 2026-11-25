import Lax793645Proofs.Simplifications.OneAsymmetricCommonProjection
import Lax793645Proofs.Simplifications.EquivariantProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {q : Format} {d e : Rates} {b b' : Bool}

/-- The one-frame overlap theorem in finite-cell form. Both leaves are
sampled independently; the two filters can depend on their ordered pair. -/
theorem one_successful_finite_projection (wA : Quill p q d b) (wB : Quill p q e b')
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hA : wA.moral t z) (hB : wB.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ r : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (OneUnit p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (a : Λ→Charts p n d) (a' : Λ→Charts p n e),
      ∃ P : KeyCoordinates (KeySlots p t) (M*n)→Fin r,
        ∀ F G : Λ×Λ→OneUnit p n (M*n)→Prop,
        let ν:=unifOn (oneOwnPart t z)
        let A l:=oneSales wA t z (π l.1) (F l) m (a l.1)
        let B l:=oneSales wB t z (π l.2) (G l) m (a' l.2)
        avg (pairW μ μ) (fun l=>dip ν (banner ν P (density ν (A l)))
          (banner ν P (density ν (B l))))≤
        avg (pairW μ μ) (fun l=>overlap ν (A l) (B l))+ε := by
  obtain ⟨S,hcal⟩:=one_asymmetric_successful_common_projection wA wB t z hA hB hp M hM c ε hε
  refine ⟨Fintype.card (Vec (Fin S)),?_⟩
  filter_upwards [hcal] with n hn m hN Λ _ μ hμ π hπ hcap a a'
  obtain ⟨s,hs,C,hC⟩:=hn m hN Λ μ hμ π hπ hcap a a'
  have hcard : Fintype.card (Vec (Fin s))≤Fintype.card (Vec (Fin S)) := by
    simp only [Vec,Fintype.card_fun,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) hs
  let enc : Vec (Fin s)→Fin (Fintype.card (Vec (Fin S))):=
    (Fin.castLE hcard)∘Fintype.equivFin _
  have henc : Injective enc:= (Fin.castLE_injective hcard).comp (Fintype.equivFin _).injective
  refine ⟨enc∘C.mulVec,?_⟩
  intro F G ν A B
  simp_rw [banner_injective_output ν _ C.mulVec enc henc]
  exact hC F G

end
end Lax793645Proofs.Simplifications
