import Lax793645Proofs.Simplifications.SuccessfulLinearQueries
import Lax793645Proofs.Simplifications.EquivariantProjection
import Lax793645Proofs.Simplifications.LinearPartitionPaints
import Lax793645Proofs.Simplifications.SuccessfulFiniteProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {q : Format} {d : Rates} {side : Bool}

/-- One partition per leaf approximates every orientation filter. Every
union of its cells is an exact bounded sum of products of unary tests. -/
theorem successful_product_partition (w : Quill p q d side)
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hw : w.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ ε : ℝ,0<ε → ∃ r paints : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ s : Charts p n d,∃ P : Keys (p:=p) t (M*n)→Fin r,
        (∀ H : Fin r→Prop,Template.design (w.pen t) (fun x=>ind (H (P x))) 1 paints) ∧
        ∀ F : UnitType p n (M*n)→Prop,
        let ν:=lawNu p (M*n) t z
        let D:=density ν (w.sales t z π F m s)
        (∀ x,0≤banner ν P D x ∧ banner ν P D x≤B) ∧
          lcost ν D (banner ν P D)≤ε := by
  obtain ⟨B,hB,hcal⟩:=successful_query_linear_partition w t z hw hp M hM c
  refine ⟨B,hB,fun ε hε=>?_⟩
  obtain ⟨R,hR⟩:=hcal ε hε
  refine ⟨Fintype.card (Vec (Fin R)),Fintype.card (Messenger q→Vec (Fin R)),?_⟩
  filter_upwards [hR] with n hn m hN π hπ hcap s
  obtain ⟨a,ha,C,hC⟩:=hn m hN π hπ hcap s
  have hcard : Fintype.card (Vec (Fin a))≤Fintype.card (Vec (Fin R)) := by
    simp only [Vec,Fintype.card_fun,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) ha
  let E:=queryCoordinateEquiv t (M*n)
  let enc : Vec (Fin a)→Fin (Fintype.card (Vec (Fin R))):=
    (Fin.castLE hcard)∘Fintype.equivFin _
  have henc : Injective enc:=(Fin.castLE_injective hcard).comp (Fintype.equivFin _).injective
  let P : Keys (p:=p) t (M*n)→Fin (Fintype.card (Vec (Fin R))):=enc∘C.mulVec∘E.symm
  have hsize : Fintype.card (Messenger q→Vec (Fin a))≤Fintype.card (Messenger q→Vec (Fin R)) := by
    simpa only [Fintype.card_fun] using Nat.pow_le_pow_left hcard (Fintype.card (Messenger q))
  refine ⟨P,fun H=>?_,?_⟩
  · have hh:=linear_key_test_design (w.pen t) C (fun x=>ind (H (enc x)))
      (fun x=>by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _)
    exact Template.design_mono (w.pen t) _ 1 _ _ zero_le_one hsize hh
  intro F ν D
  let ν' : Wgt (KeyCoordinates (KeySlots p t) (M*n)):=
    unifOn (queryReferenceSet (w.pen t) z (M*n))
  let D':=density ν' (mapW (w.sales t z π F m s) E.symm)
  have hν : mapW ν E.symm=ν':=query_reference_coordinates t z (M*n)
  have hD : D'=D∘E := by
    dsimp only [D']
    rw [←hν,density_equivalence]
    rfl
  have hproj : (banner ν' C.mulVec D')∘E.symm=banner ν P D := by
    have he:=banner_equivalence_input E.symm ν D C.mulVec
    rw [hν,Equiv.symm_symm,←hD] at he
    rw [show P=enc∘(C.mulVec∘E.symm) from rfl,banner_injective_output ν D _ enc henc]
    exact he
  have hc:=hC F
  change (∀ x,0≤banner ν P D x ∧ banner ν P D x≤B) ∧ lcost ν D (banner ν P D)≤ε
  constructor
  · intro x
    rw [←hproj]
    exact hc.1 (E.symm x)
  · have he : lcost ν D (banner ν P D)=lcost ν' D' (banner ν' C.mulVec D') := by
      change avg ν (fun x=>|D x-banner ν P D x|)=
        avg ν' (fun x=>|D' x-banner ν' C.mulVec D' x|)
      rw [←hν,mapW_avg,hν]
      change avg ν (fun x=>|D x-banner ν P D x|)=
        avg ν (fun x=>|D' (E.symm x)-banner ν' C.mulVec D' (E.symm x)|)
      apply avg_congr
      intro x _
      have hd : D' (E.symm x)=D x:=by rw [hD]; simp
      rw [hd,←hproj]
      rfl
    rw [he]
    exact hc.2

end
end Lax793645Proofs.Simplifications
