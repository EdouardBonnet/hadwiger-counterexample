import Lax793645Proofs.Simplifications.QueryLinearPartitions
import Lax793645Proofs.Simplifications.PrintedStatusComparison
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PairedMassIdentities
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SurrogateQueryScores

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}

theorem mixture_cut_density {A B : Type} [Fintype A] [Fintype B]
    (ν : Wgt B) (S : B→Prop) (t : Wgt A) (p : A→Wgt B) :
    mixW t (fun i=>density ν (subW (p i) S))=density ν (subW (mixW t p) S) := by
  funext x
  change avg t (fun i=>p i x*ind (S x)/ν x)=avg t (fun i=>p i x)*ind (S x)/ν x
  rw [avg_div,avg_mul]

def quillNominalFlags (w : Quill p q d b) (t : Tagging p (Messenger q))
    (s : Charts p n d) (m : Mixer p n) (x : Inputs p n (Messenger q)) :
    NominalAmounts p q d b×Bool :=
  (nominalPrinted b s t w.sel w.flav m x,decide (((w.pen t).draw x).reads w.script m))

def quillFlagAccept (w : Quill p q d b) (P : UnitType p n N→Prop)
    (o : UnitType p n N) (a : (NominalAmounts p q d b×Bool)×(Messenger q→F)) : Prop :=
  P o ∧ joinPrinted a.1.1 a.2=w.amp ∧ a.1.2=true

theorem deposit_flag_separation (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (s : Charts p n d) (m : Mixer p n)
    (P : UnitType p n N→Prop) (o : UnitType p n N) (x : Inputs p n (Messenger q)) :
    (P o ∧ w.deposit t z m o s x) ↔
      quillFlagAccept w P o (queryFlags (w.pen t) (quillNominalFlags w t s m) o x) ∧
        queryReferenceSet (w.pen t) z N (templateKeyCoordinates (w.pen t) o x) := by
  have he : queryFromCoordinates t N (templateKeyCoordinates (w.pen t) o x)=
      (w.pen t).resultKey o x := by
    change (queryCoordinateEquiv t N) ((queryCoordinateEquiv t N).symm ((w.pen t).resultKey o x))=_
    exact (queryCoordinateEquiv t N).apply_symm_apply _
  simp only [Quill.deposit,quillFlagAccept,queryFlags,quillNominalFlags,queryReferenceSet,
    printed_separation,he,decide_eq_true_eq,Template.resultKey]
  tauto

/-- The densities approximated by the linear theorem are exactly the
existing successful-query measures, including the binary prescriptions. -/
theorem sales_coordinate_flags (w : Quill p q d b) (t : Tagging p (Messenger q))
    [DecidableEq (KeySlots p t)] (z : Messenger q→F) (s : Charts p n d) (m : Mixer p n)
    (π : Wgt (UnitType p n N)) (P : UnitType p n N→Prop) :
    mapW (w.sales t z π P m s) (queryCoordinateEquiv t N).symm=
      subW (flaggedW π ((w.pen t).state z n)
        (queryFlags (w.pen t) (quillNominalFlags w t s m))
        (templateKeyCoordinates (w.pen t)) (quillFlagAccept w P))
        (queryReferenceSet (w.pen t) z N) := by
  funext y
  change avg (w.sales t z π P m s) (fun k=>ind ((queryCoordinateEquiv t N).symm k=y))=_
  rw [w.sales_mean π s t z m P]
  unfold subW flaggedW
  change avg π (fun o=>ind (P o)*Quill.prowl w s t z m o
    (fun k=>ind ((queryCoordinateEquiv t N).symm k=y)))=
    avg π (fun o=>mapW (fun x=>((w.pen t).state z n) x*
      ind (quillFlagAccept w P o (queryFlags (w.pen t) (quillNominalFlags w t s m) o x)))
      (templateKeyCoordinates (w.pen t) o) y)*ind (queryReferenceSet (w.pen t) z N y)
  rw [←avg_mul]
  apply avg_congr
  intro o _
  unfold Quill.prowl
  rw [←avg_mul']
  unfold mapW pr
  change avg ((w.pen t).state z n) (fun x=>ind (P o)*(ind (w.deposit t z m o s x)*
    ind ((queryCoordinateEquiv t N).symm ((w.pen t).resultKey o x)=y)))=
    avg (fun x=>((w.pen t).state z n) x*
      ind (quillFlagAccept w P o (queryFlags (w.pen t) (quillNominalFlags w t s m) o x)))
      (fun x=>ind (templateKeyCoordinates (w.pen t) o x=y))*ind (queryReferenceSet (w.pen t) z N y)
  unfold avg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  have hh:=deposit_flag_separation w t z s m P o x
  have hkey : templateKeyCoordinates (w.pen t) o x=
      (queryCoordinateEquiv t N).symm ((w.pen t).resultKey o x):=rfl
  by_cases he : templateKeyCoordinates (w.pen t) o x=y
  · have he' := hkey.symm.trans he
    simp only [ind_one he,ind_one he',mul_one]
    have hi:=congrArg ind (propext hh)
    rw [ind_and,ind_and,he] at hi
    nlinarith only [congrArg (fun a=>((w.pen t).state z n) x*a) hi]
  · have he' : (queryCoordinateEquiv t N).symm ((w.pen t).resultKey o x)≠y:=fun h=>he (hkey.trans h)
    simp only [ind_zero he,ind_zero he',mul_zero,zero_mul]

theorem product_input_cap {I X : Type} [Fintype I] [DecidableEq I] [Fintype X]
    (w : I→Wgt X) (hw : ∀ i x,0≤w i x) (C : ℝ)
    (hcap : ∀ i x,w i x≤C*unif x) (x : I→X) :
    prodW w x≤C^Fintype.card I*unif x := by
  have hh:=Finset.prod_le_prod (s:=Finset.univ)
    (fun i _=>hw i (x i)) (fun i _=>hcap i (x i))
  have hu : (∏ i : I,(unif : Wgt X) (x i))=unif x:=congrFun draws_unif.symm x
  exact hh.trans_eq (by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,hu])

theorem successful_density_catalog (w : Quill p q d b) (t : Tagging p (Messenger q))
    [DecidableEq (KeySlots p t)] (z : Messenger q→F) (s : Charts p n d) (m : Mixer p n)
    (π : Wgt (UnitType p n N)) (hπ : IsLaw π) (hκ : IsLaw ((w.pen t).state z n))
    (ν : Wgt (KeyCoordinates (KeySlots p t) N)) (F : UnitType p n N→Prop) :
    catalog (colored π ((w.pen t).state z n)
      (queryFlags (w.pen t) (quillNominalFlags w t s m)))
      (coloredCutDensities ν ((w.pen t).state z n)
        (queryFlags (w.pen t) (quillNominalFlags w t s m))
        (templateKeyCoordinates (w.pen t)) (queryReferenceSet (w.pen t) z N))
      (density ν (mapW (w.sales t z π F m s) (queryCoordinateEquiv t N).symm)) := by
  let v:=queryFlags (N:=N) (w.pen t) (quillNominalFlags w t s m)
  let K:=queryReferenceSet (w.pen t) z N
  obtain ⟨u,hu,hucap,he⟩:=flag_catalog (templateKeyCoordinates (w.pen t)) v
    (quillFlagAccept w F) hκ hπ
  refine ⟨u,hu,hucap,?_⟩
  rw [sales_coordinate_flags]
  change density ν (subW (flaggedW π ((w.pen t).state z n) v
    (templateKeyCoordinates (w.pen t)) (quillFlagAccept w F)) K)=_
  rw [he,←mixture_cut_density]
  rfl

/-- Every bounded linear partition has bounded successful-query
densities, uniformly over the number of equations chosen later. -/
theorem successful_linear_density_bound (w : Quill p q d b)
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hw : w.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (s : Charts p n d) (r : ℕ),r≤R →
      ∀ (P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p t)) (F : UnitType p n (M*n)→Prop),
      let ν:=unifOn (queryReferenceSet (w.pen t) z (M*n))
      let D:=density ν (mapW (w.sales t z π F m s) (queryCoordinateEquiv t (M*n)).symm)
      ∀ x,0≤banner ν P.mulVec D x ∧ banner ν P.mulVec D x≤B := by
  obtain ⟨B,hB,hcal⟩:=query_linear_energy_calendar
    (Y:=(NominalAmounts p q d b×Bool)×(Messenger q→F)) (w.pen t) M hM c
  refine ⟨B+1,by linarith,fun R=>?_⟩
  filter_upwards [hcal R,eventually_ge_atTop (2*p.r)]
    with n hn hnage m hN π hπ hcap s r hr P F ν D
  let κ:=w.policies t z n
  have hκ i : IsLaw (κ i):=Appearance.witLaw (w.allure_apt t z hw i) hp hnage
  let v:=queryFlags (N:=M*n) (w.pen t) (quillNominalFlags w t s m)
  have hh:=((hn m hN π hπ hcap κ hκ (fun i=>scopedZ_bit p n _ _ _ (hκ i)) z v).2 r hr P).2
  obtain ⟨u,hu,hucap,he⟩:=successful_density_catalog w t z s m π hπ (prodW_law hκ) ν F
  dsimp only [D]
  rw [he]
  exact hh u hu hucap

/-- A single bounded linear partition handles all orientation filters of
the existing successful-query measure, with the original status and
binary-prescription definitions. -/
theorem successful_query_linear_partition (w : Quill p q d b)
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hw : w.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ ε : ℝ,0<ε → ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ s : Charts p n d,
      let ν:=unifOn (queryReferenceSet (w.pen t) z (M*n))
      ∃ r : ℕ,r≤R ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p t),
        ∀ F : UnitType p n (M*n)→Prop,
        let D:=density ν (mapW (w.sales t z π F m s) (queryCoordinateEquiv t (M*n)).symm)
        (∀ x,0≤banner ν P.mulVec D x ∧ banner ν P.mulVec D x≤B) ∧
        lcost ν D (banner ν P.mulVec D)≤ε := by
  letI : Nonempty (NominalAmounts p q d b):=⟨fun _=>(0,0)⟩
  let L:=((scanPrice p)⁻¹)^Fintype.card (Messenger q)
  have hL : 0<L:=pow_pos (inv_pos.mpr (scanPrice_pos p)) _
  obtain ⟨B,hB,hcal⟩:=query_bounded_linear_partition
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
    (fun i=>scopedZ_bit p n _ _ _ (hκ i)) hinput z (quillNominalFlags w t s m)
  refine ⟨r,hr,P,fun F=>?_⟩
  let v:=queryFlags (N:=M*n) (w.pen t) (quillNominalFlags w t s m)
  let K:=queryReferenceSet (w.pen t) z (M*n)
  have hcat:=flag_catalog (templateKeyCoordinates (w.pen t)) v (quillFlagAccept w F)
    (prodW_law hκ) hπ
  obtain ⟨u,hu,hucap,he⟩:=hcat
  have hd : density ν (mapW (w.sales t z π F m s) (queryCoordinateEquiv t (M*n)).symm)=
      mixW u (coloredCutDensities ν (prodW κ) v (templateKeyCoordinates (w.pen t)) K) := by
    rw [sales_coordinate_flags]
    change density ν (subW (flaggedW π (prodW κ) v (templateKeyCoordinates (w.pen t))
      (quillFlagAccept w F)) K)=_
    rw [he,←mixture_cut_density]
    rfl
  rw [hd]
  exact hP u hu hucap

end
end Lax793645Proofs.Simplifications
