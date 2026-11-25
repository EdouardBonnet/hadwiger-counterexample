import Lax793645Proofs.Simplifications.OneQueryLinearPartitions
import Lax793645Proofs.Simplifications.OnePrintedStatusComparison
import Lax793645Proofs.Simplifications.SuccessfulLinearQueries
import Lax793645Proofs.Simplifications.ReducedMixers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}

/-- The finite nominal flags use the canonical prescriptions of the reduced
mixer family. They are fixed before the orientation is sampled. -/
def oneQuillNominalFlags (w : Quill p q d b) (t : Tagging p (Messenger q))
    (s : Charts p n d) (m : Mixer p n) (x : Inputs p n (Messenger q)) :
    NominalAmounts p q d b×Bool :=
  (nominalPrinted b s t w.sel w.flav m x,
    decide (((w.pen t).draw x).reads (reducedScript w.script) m))

def oneQuillFlagAccept (w : Quill p q d b) (P : OneUnit p n N→Prop)
    (o : OneUnit p n N) (a : (NominalAmounts p q d b×Bool)×(Messenger q→F)) : Prop :=
  P o ∧ joinPrinted a.1.1 a.2=w.amp ∧ a.1.2=true

/-- Actual successful queries in ambient key coordinates. The reference
cut imposes the quadratic Gram equations; all other tests remain in the
finite nominal/parity status, including the binary prescriptions. -/
def oneSales (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (π : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (m : Mixer p n) (s : Charts p n d) : Wgt (KeyCoordinates (KeySlots p t) N) :=
  subW (flaggedW π ((w.pen t).state z n)
    (oneQueryFlags (w.pen t) (oneQuillNominalFlags w t s m))
    (oneTemplateCoordinates (w.pen t)) (oneQuillFlagAccept w P))
    (oneQueryReferenceSet (w.pen t) z N)

theorem one_sales_mean (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (π : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (m : Mixer p n) (s : Charts p n d) (f : Wgt (KeyCoordinates (KeySlots p t) N)) :
    avg (oneSales w t z π P m s) f=avg π (fun o=>avg ((w.pen t).state z n)
      (fun x=>f (oneTemplateCoordinates (w.pen t) o x)*
        ind (P o ∧ onePrinted b s t w.sel w.flav m o x=w.amp ∧
          ((w.pen t).draw x).reads (reducedScript w.script) m ∧
          oneOwnPart t z (oneTemplateCoordinates (w.pen t) o x)))) := by
  unfold oneSales subW flaggedW
  change avg (fun k=>avg π (fun o=>mapW
    (fun x=>((w.pen t).state z n) x*
      ind (oneQuillFlagAccept w P o (oneQueryFlags (w.pen t) (oneQuillNominalFlags w t s m) o x)))
        (oneTemplateCoordinates (w.pen t) o) k)*ind (oneQueryReferenceSet (w.pen t) z N k)) f=_
  unfold avg
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [mapW,pr,avg]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (oneTemplateCoordinates (w.pen t) o x)]
  · simp only [ind_true,mul_one]
    have he : oneQuillFlagAccept w P o (oneQueryFlags (w.pen t) (oneQuillNominalFlags w t s m) o x) ∧
        oneQueryReferenceSet (w.pen t) z N (oneTemplateCoordinates (w.pen t) o x) ↔
      P o ∧ onePrinted b s t w.sel w.flav m o x=w.amp ∧
        ((w.pen t).draw x).reads (reducedScript w.script) m ∧
        oneOwnPart t z (oneTemplateCoordinates (w.pen t) o x) := by
      simp only [oneQuillFlagAccept,oneQueryFlags,oneQuillNominalFlags,onePrinted,
        oneQueryReferenceSet,decide_eq_true_eq]
      tauto
    have hi:=congrArg ind (propext he)
    rw [ind_and] at hi
    rw [←hi]
    ring
  · intro k _ hk
    rw [ind_zero (Ne.symm hk)]
    ring
  · simp

theorem one_sales_nonneg (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (π : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (m : Mixer p n) (s : Charts p n d) (hπ : ∀ o,0≤π o) :
    ∀ x,0≤oneSales w t z π P m s x := by
  intro x
  unfold oneSales subW
  apply mul_nonneg _ (ind_nonneg _)
  apply avg_nonneg hπ
  intro o
  apply map_nz
  intro y
  exact mul_nonneg (prodW_nonneg (fun _=>normW_nonneg (subW_nonneg (spins_law ..).nz _)) _) (ind_nonneg _)

theorem one_successful_density_catalog (w : Quill p q d b) (t : Tagging p (Messenger q))
    [DecidableEq (KeySlots p t)] (z : Messenger q→F) (s : Charts p n d) (m : Mixer p n)
    (π : Wgt (OneUnit p n N)) (hπ : IsLaw π) (hκ : IsLaw ((w.pen t).state z n))
    (ν : Wgt (KeyCoordinates (KeySlots p t) N)) (F : OneUnit p n N→Prop) :
    catalog (colored π ((w.pen t).state z n)
      (oneQueryFlags (w.pen t) (oneQuillNominalFlags w t s m)))
      (coloredCutDensities ν ((w.pen t).state z n)
        (oneQueryFlags (w.pen t) (oneQuillNominalFlags w t s m))
        (oneTemplateCoordinates (w.pen t)) (oneQueryReferenceSet (w.pen t) z N))
      (density ν (oneSales w t z π F m s)) := by
  let v:=oneQueryFlags (N:=N) (w.pen t) (oneQuillNominalFlags w t s m)
  let K:=oneQueryReferenceSet (w.pen t) z N
  obtain ⟨u,hu,hucap,he⟩:=flag_catalog (oneTemplateCoordinates (w.pen t)) v
    (oneQuillFlagAccept w F) hκ hπ
  refine ⟨u,hu,hucap,?_⟩
  unfold oneSales
  change density ν (subW (flaggedW π ((w.pen t).state z n) v
    (oneTemplateCoordinates (w.pen t)) (oneQuillFlagAccept w F)) K)=_
  rw [he,←mixture_cut_density]
  rfl

/-- Every bounded linear partition has bounded successful-query
densities, uniformly over the number of equations chosen later. -/
theorem one_successful_linear_density_bound (w : Quill p q d b)
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hw : w.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (s : Charts p n d) (r : ℕ),r≤R →
      ∀ (P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p t)) (F : OneUnit p n (M*n)→Prop),
      let ν:=unifOn (oneQueryReferenceSet (w.pen t) z (M*n))
      let D:=density ν (oneSales w t z π F m s)
      ∀ x,0≤banner ν P.mulVec D x ∧ banner ν P.mulVec D x≤B := by
  let L:=((scanPrice p)⁻¹)^Fintype.card (Messenger q)
  have hL : 0<L:=pow_pos (inv_pos.mpr (scanPrice_pos p)) _
  obtain ⟨B,hB,hcal⟩:=one_query_linear_energy_calendar
    (Y:=(NominalAmounts p q d b×Bool)×(Messenger q→F)) (w.pen t) M hM c L hL
  refine ⟨B+1,by linarith,fun R=>?_⟩
  filter_upwards [hcal R,eventually_ge_atTop (2*p.r)]
    with n hn hnage m hN π hπ hcap s r hr P F ν D
  let κ:=w.policies t z n
  have hκ i : IsLaw (κ i):=Appearance.witLaw (w.allure_apt t z hw i) hp hnage
  have hinput x : prodW κ x≤L*unif x :=
    product_input_cap κ (fun i=>(hκ i).nz) ((scanPrice p)⁻¹)
      (fun i x=>dialCap p _ _ _ hp hnage (w.allure_apt t z hw i) x) x
  let v:=oneQueryFlags (N:=M*n) (w.pen t) (oneQuillNominalFlags w t s m)
  have hh:=((hn m hN π hπ hcap κ hκ (fun i=>scopedZ_bit p n _ _ _ (hκ i))
    hinput z v).2 r hr P).2
  obtain ⟨u,hu,hucap,he⟩:=one_successful_density_catalog w t z s m π hπ (prodW_law hκ) ν F
  dsimp only [D]
  rw [he]
  exact hh u hu hucap

/-- A single bounded linear partition handles all orientation filters of
the existing successful-query measure, with the original status and
binary-prescription definitions. -/
theorem one_successful_query_linear_partition (w : Quill p q d b)
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hw : w.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ ε : ℝ,0<ε → ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ s : Charts p n d,
      let ν:=unifOn (oneQueryReferenceSet (w.pen t) z (M*n))
      ∃ r : ℕ,r≤R ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p t),
        ∀ F : OneUnit p n (M*n)→Prop,
        let D:=density ν (oneSales w t z π F m s)
        (∀ x,0≤banner ν P.mulVec D x ∧ banner ν P.mulVec D x≤B) ∧
        lcost ν D (banner ν P.mulVec D)≤ε := by
  letI : Nonempty (NominalAmounts p q d b):=⟨fun _=>(0,0)⟩
  let L:=((scanPrice p)⁻¹)^Fintype.card (Messenger q)
  have hL : 0<L:=pow_pos (inv_pos.mpr (scanPrice_pos p)) _
  obtain ⟨B,hB,hcal⟩:=one_query_bounded_linear_partition
    (A:=NominalAmounts p q d b×Bool) (w.pen t) M hM c L hL
  refine ⟨B,hB,fun ε hε=>?_⟩
  obtain ⟨R,hR⟩:=hcal ε hε
  refine ⟨R,?_⟩
  filter_upwards [hR,eventually_ge_atTop (2*p.r)] with n hn hnage m hN π hπ hcap s ν
  let κ:=w.policies t z n
  have hκ i : IsLaw (κ i):=Appearance.witLaw (w.allure_apt t z hw i) hp hnage
  have hinput x : prodW κ x≤L*unif x :=
    product_input_cap κ (fun i=>(hκ i).nz) ((scanPrice p)⁻¹)
      (fun i x=>dialCap p _ _ _ hp hnage (w.allure_apt t z hw i) x) x
  obtain ⟨r,hr,P,hP⟩:=hn m hN π hπ hcap κ hκ
    (fun i=>scopedZ_bit p n _ _ _ (hκ i)) hinput z (oneQuillNominalFlags w t s m)
  refine ⟨r,hr,P,fun F=>?_⟩
  let v:=oneQueryFlags (N:=M*n) (w.pen t) (oneQuillNominalFlags w t s m)
  let K:=oneQueryReferenceSet (w.pen t) z (M*n)
  have hcat:=flag_catalog (oneTemplateCoordinates (w.pen t)) v (oneQuillFlagAccept w F)
    (prodW_law hκ) hπ
  obtain ⟨u,hu,hucap,he⟩:=hcat
  have hd : density ν (oneSales w t z π F m s)=
      mixW u (coloredCutDensities ν (prodW κ) v (oneTemplateCoordinates (w.pen t)) K) := by
    unfold oneSales
    change density ν (subW (flaggedW π (prodW κ) v (oneTemplateCoordinates (w.pen t))
      (oneQuillFlagAccept w F)) K)=_
    rw [he,←mixture_cut_density]
    rfl
  rw [hd]
  exact hP u hu hucap

end
end Lax793645Proofs.Simplifications
