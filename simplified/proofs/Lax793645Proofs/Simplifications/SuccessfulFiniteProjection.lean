import Lax793645Proofs.Simplifications.EquivariantProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {q : Format} {d e : Rates} {b b' : Bool}

theorem query_reference_coordinates (t : Tagging p (Messenger q))
    [DecidableEq (KeySlots p t)] (z : Messenger q→F) (N : ℕ) :
    mapW (lawNu p N t z) (queryCoordinateEquiv t N).symm=
      unifOn (fun x=>ownPart t z (queryFromCoordinates t N x)) := by
  have hh:=on_equiv (queryCoordinateEquiv t N) (ownPart (p:=p) (N:=N) t z)
  change mapW (unifOn (fun x=>ownPart t z (queryFromCoordinates t N x)))
    (queryCoordinateEquiv t N)=lawNu p N t z at hh
  funext x
  rw [mapW_equiv_val,←hh,mapW_equiv_val,Equiv.symm_symm,Equiv.symm_apply_apply]

/-- The common linear projection, expressed in the existing key spaces
and finite-cell interface used by the scalar assembly. -/
theorem successful_finite_projection (wA : Quill p q d b) (wB : Quill p q e b')
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hA : wA.moral t z) (hB : wB.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
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
        avg (pairW μ μ) (fun l=>dip ν (banner ν P (density ν (A l)))
          (banner ν P (density ν (B l))))≤
        avg (pairW μ μ) (fun l=>overlap ν (A l) (B l))+ε := by
  obtain ⟨S,hcal⟩:=asymmetric_successful_common_projection wA wB t z hA hB hp M hM c ε hε
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
  have hproj (u v : Wgt (Keys (p:=p) t (M*n))) :
      dip ν (banner ν P (density ν u)) (banner ν P (density ν v))=
        dip (mapW ν E.symm)
          (banner (mapW ν E.symm) C.mulVec (density (mapW ν E.symm) (mapW u E.symm)))
          (banner (mapW ν E.symm) C.mulVec (density (mapW ν E.symm) (mapW v E.symm))) := by
    have hp : P=enc∘(C.mulVec∘E.symm):=rfl
    rw [hp,banner_injective_output ν (density ν u) _ enc henc,
      banner_injective_output ν (density ν v) _ enc henc]
    exact (projected_overlap_equivalence E.symm ν u v C.mulVec).symm
  have hov (u v : Wgt (Keys (p:=p) t (M*n))) : overlap ν u v=
      dip (mapW ν E.symm) (density (mapW ν E.symm) (mapW u E.symm))
        (density (mapW ν E.symm) (mapW v E.symm)) := by
    rw [density_equivalence,density_equivalence,dip_equivalence]
    rfl
  have hh:=hC F G
  change avg (pairW μ μ) (fun l=>dip ν (banner ν P (density ν (A l)))
    (banner ν P (density ν (B l))))≤avg (pairW μ μ) (fun l=>overlap ν (A l) (B l))+ε
  simp_rw [hproj,hov,hν]
  exact hh

end
end Lax793645Proofs.Simplifications
