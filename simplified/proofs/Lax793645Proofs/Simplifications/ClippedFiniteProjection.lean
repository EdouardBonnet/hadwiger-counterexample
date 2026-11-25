import Lax793645Proofs.Simplifications.EquivariantRebate
import Lax793645Proofs.Simplifications.ClippedSuccessfulProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {q : Format} {d e : Rates} {b b' : Bool}

/-- The common linear projection, expressed in the existing key spaces
and finite-cell interface used by the scalar assembly. -/
theorem clipped_successful_finite_projection (wA : Quill p q d b) (wB : Quill p q e b')
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hA : wA.moral t z) (hB : wB.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c T ε : ℝ) (hT : 0<T) (hε : 0<ε) :
    ∃ r : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (UnitType p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (a : Λ→Charts p n d) (a' : Λ→Charts p n e),
      ∃ P : Keys (p:=p) t (M*n)→Fin r,
        ∀ F G : Λ×Λ→UnitType p n (M*n)→Prop,
        let ν:=lawNu p (M*n) t z
        let A l:=wA.sales t z (π l.1) (F l) m (a l.1)
        let B l:=wB.sales t z (π l.2) (G l) m (a' l.2)
        avg (pairW μ μ) (fun l=>|rebate ν (mcut T ν (A l)) (mcut T ν (B l)) P|)≤ε := by
  obtain ⟨S,hcal⟩:=clipped_successful_common_projection wA wB t z hA hB hp M hM c T ε hT hε
  refine ⟨Fintype.card (Vec (Fin S)),?_⟩
  filter_upwards [hcal] with n hn m hN Λ _ μ hμ π hπ hcap a a'
  obtain ⟨s,hs,C,hC⟩:=hn m hN Λ μ hμ π hπ hcap a a'
  have hcard : Fintype.card (Vec (Fin s))≤Fintype.card (Vec (Fin S)) := by
    simp only [Vec,Fintype.card_fun,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) hs
  let E:=queryCoordinateEquiv t (M*n)
  let enc : Vec (Fin s)→Fin (Fintype.card (Vec (Fin S))):=
    (Fin.castLE hcard)∘Fintype.equivFin _
  have henc : Injective enc:= (Fin.castLE_injective hcard).comp (Fintype.equivFin _).injective
  let P : Keys (p:=p) t (M*n)→Fin (Fintype.card (Vec (Fin S))):=enc∘C.mulVec∘E.symm
  refine ⟨P,?_⟩
  intro F G ν A B
  have hν : mapW ν E.symm=unifOn (queryReferenceSet (wA.pen t) z (M*n)):=
    query_reference_coordinates t z (M*n)
  have hreb (u v : Wgt (Keys (p:=p) t (M*n))) :
      rebate ν (mcut T ν u) (mcut T ν v) P=
        rebate (mapW ν E.symm) (mcut T (mapW ν E.symm) (mapW u E.symm))
          (mcut T (mapW ν E.symm) (mapW v E.symm)) C.mulVec := by
    have hp : P=enc∘(C.mulVec∘E.symm):=rfl
    rw [hp,rebate_injective_output ν _ _ _ enc henc,mcut_equivalence,mcut_equivalence,
      rebate_equivalence]
  have hh:=hC F G
  change avg (pairW μ μ) (fun l=>|rebate ν (mcut T ν (A l)) (mcut T ν (B l)) P|)≤ε
  simp_rw [hreb,hν]
  exact hh

end
end Lax793645Proofs.Simplifications
