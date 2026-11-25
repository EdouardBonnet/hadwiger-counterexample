import Lax793645Proofs.Simplifications.OneRejectedCommonProjection
import Lax793645Proofs.Simplifications.EquivariantProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Padding adds zero equations and does not change a partition. -/
def linearPad {r R : ℕ} (_ : r≤R) : Vec (Fin r)→ₗ[F]Vec (Fin R) where
  toFun x i:=if hi:i.val<r then x ⟨i.val,hi⟩ else 0
  map_add' x y:=by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x:=by ext i; simp only [Pi.smul_apply]; split_ifs <;> simp

theorem linear_pad_injective {r R : ℕ} (h : r≤R) : Injective (linearPad h) := by
  intro x y hxy
  funext i
  have hh:=congrFun hxy (Fin.castLE h i)
  simpa only [linearPad,LinearMap.coe_mk,AddHom.coe_mk,Fin.coe_castLE,dif_pos i.isLt] using hh

variable {p : Shape} {q : Format} {d e : Rates} {b b' : Bool}

theorem one_fixed_rejected_common_projection (wA : Quill p q d b) (wB : Quill p q e b')
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hA : wA.moral t z) (hB : wB.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ S : ℕ,∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (OneUnit p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (a : Λ→Charts p n d) (a' : Λ→Charts p n e),
      let ν:=unifOn (oneQueryReferenceSet (wA.pen t) z (M*n))
      let DA (l : Λ) (F : OneUnit p n (M*n)→Prop):=
        density ν (oneSales wA t z (π l) F m (a l))
      let DB (l : Λ) (F : OneUnit p n (M*n)→Prop):=
        density ν (oneSales wB t z (π l) F m (a' l))
      ∃ L : KeyCoordinates (KeySlots p t) (M*n)→ₗ[F]Vec (Fin S),
        ∀ F G : Λ×Λ→OneUnit p n (M*n)→Prop,
        ∀ QA QB : Λ×Λ→Wgt (KeyCoordinates (KeySlots p t) (M*n)),
        (∀ l x,0≤QA l x ∧ QA l x≤oneSales wA t z (π l.1) (F l) m (a l.1) x) →
        (∀ l x,0≤QB l x ∧ QB l x≤oneSales wB t z (π l.2) (G l) m (a' l.2) x) →
        (∀ l,varOne (oneSales wA t z (π l.1) (F l) m (a l.1)) (QA l)≤δ) →
        (∀ l,varOne (oneSales wB t z (π l.2) (G l) m (a' l.2)) (QB l)≤δ) →
        avg (pairW μ μ) (fun l=>dip ν (banner ν L (DA l.1 (F l)))
          (banner ν L (DB l.2 (G l))))≤
        avg (pairW μ μ) (fun l=>overlap ν (QA l) (QB l))+ε := by
  obtain ⟨S,δ,hδ,hcal⟩:=one_rejected_successful_common_projection wA wB t z hA hB hp M hM c ε hε
  refine ⟨S,δ,hδ,?_⟩
  filter_upwards [hcal] with n hn m hN Λ _ μ hμ π hπ hcap a a' ν DA DB
  obtain ⟨s,hs,C,hC⟩:=hn m hN Λ μ hμ π hπ hcap a a'
  let L : KeyCoordinates (KeySlots p t) (M*n)→ₗ[F]Vec (Fin S):=
    (linearPad hs).comp C.mulVecLin
  refine ⟨L,fun F G QA QB hQA hQB hvarA hvarB=>?_⟩
  change avg (pairW μ μ) (fun l=>dip ν
    (banner ν ((linearPad hs)∘C.mulVec) (DA l.1 (F l)))
    (banner ν ((linearPad hs)∘C.mulVec) (DB l.2 (G l))))≤_
  simp_rw [banner_injective_output ν _ C.mulVec (linearPad hs) (linear_pad_injective hs)]
  exact hC F G QA QB hQA hQB hvarA hvarB

end
end Lax793645Proofs.Simplifications
