import Lax793645Proofs.Simplifications.OneQueryLinearPartitions
import Lax793645Proofs.Simplifications.OneKeyReferenceLaws
import Lax793645Proofs.Simplifications.EquivariantProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

private theorem uniform_coordinates {A B : Type} (i j : Fintype A) (k : Fintype B)
    (E : A≃B) (P : B→Prop) :
    @mapW A B i (@unifOn A j (P ∘ E)) E=@unifOn B k P := by
  cases Subsingleton.elim i j
  exact on_equiv E P

/-- Marginalizing all statuses gives a bounded approximation to the
unfiltered query density. It dominates every subsequently chosen flag. -/
theorem one_unfiltered_bounded_approximation (v : Template p I)
    [DecidableEq (KeySlots p v.t)] (M : ℕ) (hM : 1≤M)
    (c L : ℝ) (hL : 0<L) :
    ∃ B : ℝ,1≤B ∧ ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤L*unif x) → ∀ q : I→F,
      let ν:=oneLawNu p (M*n) v.t q
      let W:=subW (mixW π (fun o=>oneHeatMap v o w)) (oneOwnKeyPart v.t q)
      ∃ g : Wgt (OneKeys v.t (M*n)),(∀ x,0≤g x ∧ g x≤B) ∧
        lcost ν (density ν W) g≤ε := by
  obtain ⟨B,hB,hcal⟩:=one_query_bounded_linear_partition (A:=Unit) v M hM c L hL
  refine ⟨B,hB,fun ε hε=>?_⟩
  obtain ⟨R,hR⟩:=hcal ε hε
  filter_upwards [hR] with n hn m hN π hπ hcap w hw hZ hinput q ν W
  let κ:=prodW w
  have hκ : IsLaw κ:=prodW_law hw
  let f:=oneQueryFlags (N:=M*n) v (fun _ : Inputs p n I=>())
  let μ:=colored π κ f
  let K:=oneQueryReferenceSet v q (M*n)
  let ν':Wgt (KeyCoordinates (KeySlots p v.t) (M*n)):=unifOn K
  let W':=subW (mixW π (fun o=>mapW κ (oneTemplateCoordinates v o))) K
  let D':=density ν' W'
  obtain ⟨r,_,P,hP⟩:=hn m hN π hπ hcap w hw hZ hinput q (fun _=>())
  have hμ : IsLaw μ:=(colored_ultra hπ hκ (oneTemplateCoordinates v) f).law
  have hd : mixW μ (coloredCutDensities ν' κ f (oneTemplateCoordinates v) K)=D' := by
    have he : mixW μ (coloredCutDensities ν' κ f (oneTemplateCoordinates v) K)=
        density ν' (subW (mixW μ (coloredP κ f (oneTemplateCoordinates v))) K) := by
      funext x
      change avg μ (fun i=>coloredP κ f (oneTemplateCoordinates v) i x*ind (K x)/ν' x)=_
      rw [avg_div,avg_mul]
      rfl
    rw [he,colored_mixture π κ hκ (oneTemplateCoordinates v) f]
  have hh:=hP μ hμ.nz (fun _=>le_rfl)
  change (∀ x,0≤banner ν' P.mulVec _ x ∧ banner ν' P.mulVec _ x≤B) ∧
    lcost ν' _ (banner ν' P.mulVec _)≤ε at hh
  rw [hd] at hh
  let E:=oneQueryCoordinateEquiv v.t (M*n)
  have hν : mapW ν E.symm=ν' := by
    unfold ν ν' oneLawNu oneOwnKeyPart K oneQueryReferenceSet
    exact uniform_coordinates _ _ _ E.symm (oneOwnPart v.t q)
  have hmap (o : OneUnit p n (M*n)) :
      mapW (oneHeatMap v o w) E.symm=mapW κ (oneTemplateCoordinates v o) := by
    rw [oneHeatMap,map_nested]
    rfl
  have hW : mapW W E.symm=W' := by
    funext x
    rw [mapW_equiv_val]
    change mixW π (fun o=>oneHeatMap v o w) (E x)*ind (oneOwnKeyPart v.t q (E x))=
      mixW π (fun o=>mapW κ (oneTemplateCoordinates v o)) x*ind (K x)
    have he : oneOwnKeyPart v.t q (E x)=K x := by
      change oneOwnPart v.t q (E.symm (E x))=oneOwnPart v.t q x
      rw [E.symm_apply_apply]
    rw [he]
    congr 1
    apply avg_congr
    intro o _
    have hx:=congr_fun (hmap o) x
    rw [mapW_equiv_val] at hx
    exact hx
  have hD : D'=density ν W ∘ E := by
    dsimp only [D']
    rw [←hW,←hν,density_equivalence]
    rfl
  let g:=banner ν' P.mulVec D'
  refine ⟨g ∘ E.symm,fun x=>hh.1 (E.symm x),?_⟩
  have he : lcost ν (density ν W) (g ∘ E.symm)=lcost ν' D' g := by
    unfold lcost
    rw [←hν,mapW_avg]
    apply avg_congr
    intro x _
    rw [hD]
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  exact he.trans_le hh.2

end
end Lax793645Proofs.Simplifications
