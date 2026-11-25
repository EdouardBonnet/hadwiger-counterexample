import Lax793645Proofs.Simplifications.OneQueryProtection
import Lax793645Proofs.Simplifications.OneSurrogateQueryScores

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function StatusAnalysis
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A X T : Type} [Fintype A] [Fintype X] [Fintype T]

def inputHistogram (key : A→X→T) (μ : Wgt X) (ρ : Wgt A) (U : A→X→Prop) : Wgt T:=
  fun k=>avg ρ (fun a=>pr μ (fun x=>U a x ∧ key a x=k))

theorem input_histogram_total (key : A→X→T) (μ : Wgt X) (ρ : Wgt A) (U : A→X→Prop) :
    tot (inputHistogram key μ ρ U)=avg ρ (fun a=>pr μ (U a)) := by
  unfold tot inputHistogram
  rw [←avg_sum]
  simp_rw [sum_pr_tag]

theorem input_histogram_mean (key : A→X→T) (μ : Wgt X) (ρ : Wgt A)
    (U : A→X→Prop) (f : Wgt T) :
    avg (inputHistogram key μ ρ U) f=
      avg ρ (fun a=>avg μ (fun x=>f (key a x)*ind (U a x))) := by
  have he : inputHistogram key μ ρ U=mixW ρ (fun a=>mapW (subW μ (U a)) (key a)) := by
    funext k
    simp only [inputHistogram,mixW,mapW,pr_sub]
  rw [he,mixW_avg]
  simp_rw [mapW_avg]
  apply avg_congr
  intro a _
  unfold avg subW
  apply sum_congr rfl
  intro x _
  ring

theorem input_histogram_rejection (key : A→X→T) (μ : Wgt X) (ρ : Wgt A)
    (U : A→X→Prop) (G : A→Prop) (δ : ℝ) (hμ : SubLaw μ) (hρ : ∀ a,0≤ρ a)
    (hG : pr ρ (fun a=>¬G a)≤δ) :
    let p:=inputHistogram key μ ρ U
    let pg:=inputHistogram key μ ρ (fun a x=>G a ∧ U a x)
    (∀ k,0≤pg k ∧ pg k≤p k) ∧ varOne p pg≤δ := by
  intro p pg
  have hdom k : pg k≤p k:=avg_mono hρ (fun a=>pr_mono hμ.nz (fun x hx=>⟨hx.1.2,hx.2⟩))
  refine ⟨fun k=>⟨avg_nonneg hρ (fun _=>pr_nonneg hμ.nz),hdom k⟩,?_⟩
  have hv : varOne p pg=tot p-tot pg := by
    unfold varOne tot
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (hdom _))]
    rw [sum_sub_distrib]
  rw [hv,input_histogram_total,input_histogram_total,←avg_sub]
  apply (avg_mono hρ (fun a=>?_)).trans hG
  by_cases ha : G a
  · simp [ha]
  simpa [ha] using ((pr_le_tot hμ.nz : pr μ (U a)≤tot μ).trans hμ.total)

theorem weights_eq_of_tests (μ ν : Wgt X) (h : ∀ f : Wgt X,avg μ f=avg ν f) : μ=ν := by
  funext x
  exact (pr_point' μ x).symm.trans ((h (fun y=>ind (y=x))).trans (pr_point' ν x))

theorem finite_average_instances {D : Type} (i j : Fintype D) (μ f : D→ℝ) :
    @avg D i μ f=@avg D j μ f := by
  cases Subsingleton.elim i j
  rfl

theorem variation_map_equiv (e : X≃T) (μ ν : Wgt X) :
    varOne (mapW μ e) (mapW ν e)=varOne μ ν := by
  unfold varOne
  simp_rw [mapW_equiv_val]
  exact e.symm.sum_comp (fun x=>|μ x-ν x|)

variable {p : Shape} {n N K : ℕ} {q : Format} {d : Rates} {b : Bool}

def oneHistogram {I : Type} [Fintype I] (v : A→Volley p n I) (t : Tagging p I)
    (μ : Wgt (OneUnit p n N)) (ρ : Wgt A) (U : A→OneUnit p n N→Prop) : Wgt (OneKeys t N):=
  inputHistogram (fun a=>oneVolleyKeys (v a) t) μ ρ U

namespace OneQuill

def oneDeposit (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (m : Mixer p n) (o : OneUnit p n N) (s : Charts p n d) (x : Inputs p n (Messenger q)) :=
  onePrinted b s t w.sel w.flav m o x=w.amp ∧ ((w.pen t).draw x).reads (reducedScript w.script) m ∧
    oneOwnKeyPart t z (oneVolleyKeys ((w.pen t).draw x) t o)

theorem one_sales_histogram (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (m : Mixer p n) (s : Charts p n d) :
    mapW (oneSales w t z μ P m s) (oneQueryCoordinateEquiv t N)=
      oneHistogram (w.pen t).draw t μ ((w.pen t).state z n)
        (fun x o=>P o ∧ oneDeposit w t z m o s x) := by
  apply weights_eq_of_tests
  intro f
  rw [mapW_avg]
  have hp:=one_sales_prowl w t z m s μ P f
  refine ((finite_average_instances _ _ _ _).trans hp).trans ?_
  change _=avg (inputHistogram _ _ _ _) f
  rw [input_histogram_mean,avg_avg]
  apply avg_congr
  intro o _
  unfold oneProwl
  rw [←avg_mul']
  apply avg_congr
  intro x _
  simp only [oneDeposit,ind_and]
  ring

def oneGoodHistogram (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop) (m : Mixer p n) (s : Charts p n d) :=
  oneHistogram (w.pen t).draw t μ ((w.pen t).state z n)
    (fun x o=>OneProtectedInput (w.pen t) pin K x ∧ P o ∧ oneDeposit w t z m o s x)

/-- At a valid frame the key at one incident component recovers the whole
nominal point. Unused input coordinates can still vary within a fiber. -/
theorem draw_eq_of_keys_eq {I : Type} [Fintype I] [DecidableEq I] (v : Template p I)
    {m : Mixer p n} {o : OneUnit p n N} (hg : 2≤p.g) (ho : ∀ j,oneFrameLaw m (o j))
    {x y : Inputs p n I} (h : oneVolleyKeys (v.draw x) v.t o=oneVolleyKeys (v.draw y) v.t o) :
    v.draw x=v.draw y := by
  have hpar : (v.draw x).par=(v.draw y).par := by
    funext i k
    obtain ⟨e⟩ : Nonempty (TagStar (v.t i)) :=
      Fintype.card_pos_iff.mp ((card_star (v.t i)).symm ▸ tagDegree_pos hg)
    have hp := one_primal_injective (ho (v.aim i)) e.val (congrFun (congrFun h i) e)
    change point p (v.s i) ((v.draw x).par i)=point p (v.s i) ((v.draw y).par i) at hp
    simpa only [point_base_eval,baseV,Option.elim'_some] using
      congrFun hp (emptySel,some k)
  exact congrArg (fun par=>Volley.mk v.aim v.s par) hpar

private theorem printed_eq_of_draw_eq (w : Quill p q d b) (t : Tagging p (Messenger q))
    (m : Mixer p n) (o : OneUnit p n N) (s : Charts p n d)
    {x y : Inputs p n (Messenger q)} (h : (w.pen t).draw x=(w.pen t).draw y) :
    onePrinted b s t w.sel w.flav m o x=onePrinted b s t w.sel w.flav m o y := by
  funext i
  have hp : lit (w.flav i) (t i) (x i)=lit (w.flav i) (t i) (y i) :=
    congrArg (fun v : Volley p n (Messenger q)=>v.par i) h
  have hs : scan p (t i) (w.flav i) (x i)=scan p (t i) (w.flav i) (y i) := by
    funext a
    rw [scan_is p _ (w.sel i),scan_is p _ (w.sel i),hp]
  simp only [onePrinted,joinPrinted,nominalPrinted,oneQueryPValues,manager,useAtom,hp,hs]

/-- Feasibility on a full key includes the binary script and protected
independence. Each query is tested at its own orientation. -/
def feasibleKey (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) (m : Mixer p n)
    (s : Charts p n d) (o : OneUnit p n N) (k : OneKeys t N) : Prop :=
  ∃ x,oneVolleyKeys ((w.pen t).draw x) t o=k ∧
    OneProtectedInput (w.pen t) pin K x ∧ oneDeposit w t z m o s x

theorem accepted_iff_feasible_key (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (m : Mixer p n) (s : Charts p n d) (o : OneUnit p n N) (x : Inputs p n (Messenger q))
    (hg : 2≤p.g) (ho : ∀ j,oneFrameLaw m (o j)) :
    OneProtectedInput (w.pen t) pin K x ∧ oneDeposit w t z m o s x ↔
      feasibleKey w t z pin K m s o (oneVolleyKeys ((w.pen t).draw x) t o) := by
  refine ⟨fun h=>⟨x,rfl,h⟩,?_⟩
  rintro ⟨y,hy,hp,hprint,hread,hkey⟩
  have he := draw_eq_of_keys_eq (w.pen t) hg ho hy
  have hpy := printed_eq_of_draw_eq w t m o s he
  exact ⟨by simpa only [OneProtectedInput,he] using hp,hpy ▸ hprint,he ▸ hread,hy ▸ hkey⟩

/-- The accepted measure of a complete option is exactly the raw key
measure restricted to its feasible keys before averaging orientations. -/
theorem good_histogram_eq_feasible (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop) (m : Mixer p n) (s : Charts p n d)
    (hg : 2≤p.g) (ho : ∀ o,P o → ∀ j,oneFrameLaw m (o j)) (k : OneKeys t N) :
    oneGoodHistogram w t z pin K μ P m s k =
      avg μ (fun o=> mapW ((w.pen t).state z n)
        (fun x=>oneVolleyKeys ((w.pen t).draw x) t o) k *
          ind (P o ∧ feasibleKey w t z pin K m s o k)) := by
  unfold oneGoodHistogram oneHistogram inputHistogram pr
  rw [avg_avg]
  apply avg_congr
  intro o _
  rw [mapW,pr,←avg_mul]
  apply avg_congr
  intro x _
  rw [←ind_and]
  apply congrArg ind
  apply propext
  constructor
  · rintro ⟨⟨hG,hP,hD⟩,rfl⟩
    exact ⟨rfl,hP,x,rfl,hG,hD⟩
  · rintro ⟨rfl,hP,hF⟩
    obtain ⟨hG,hD⟩ := (accepted_iff_feasible_key w t z pin K m s o x hg (ho o hP)).2 hF
    exact ⟨⟨hG,hP,hD⟩,rfl⟩

def oneGoodSales (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop) (m : Mixer p n) (s : Charts p n d) :=
  mapW (oneGoodHistogram w t z pin K μ P m s) (oneQueryCoordinateEquiv t N).symm

/-- The exact reduced query measure needed by quadratic realization is
dominated by the original measure and loses exponentially small mass. -/
theorem one_good_sales_rejection (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop) (m : Mixer p n) (s : Charts p n d)
    (hμ : SubLaw μ) (hpen : OnePenSpace (w.pen t) pin K)
    (hκ : ∀ i,IsLaw (w.policies t z n i)) :
    (∀ k,0≤oneGoodSales w t z pin K μ P m s k ∧
      oneGoodSales w t z pin K μ P m s k≤oneSales w t z μ P m s k) ∧
    varOne (oneSales w t z μ P m s) (oneGoodSales w t z pin K μ P m s)≤
      bp (num (Messenger q)+(oneBaseProtectionDim p K:ℝ)-(n:ℝ)) := by
  let H:=oneHistogram (w.pen t).draw t μ ((w.pen t).state z n)
    (fun x o=>P o ∧ oneDeposit w t z m o s x)
  let G:=oneGoodHistogram w t z pin K μ P m s
  let E:=oneQueryCoordinateEquiv t N
  have hh:=input_histogram_rejection (fun x=>oneVolleyKeys ((w.pen t).draw x) t)
    μ ((w.pen t).state z n) (fun x o=>P o ∧ oneDeposit w t z m o s x)
    (OneProtectedInput (w.pen t) pin K) _ hμ (prodW_law hκ).nz
    (one_query_rejection (w.pen t) pin K hpen z hκ)
  change (∀ k,0≤G k ∧ G k≤H k) ∧ varOne H G≤_ at hh
  have he : oneSales w t z μ P m s=mapW H E.symm := by
    have hi:=one_sales_histogram w t z μ P m s
    funext k
    have hj:=congrFun hi (E k)
    rw [mapW_equiv_val,Equiv.symm_apply_apply] at hj
    rw [mapW_equiv_val]
    exact hj
  change (∀ k,0≤mapW G E.symm k ∧ mapW G E.symm k≤oneSales w t z μ P m s k) ∧ _
  rw [he]
  constructor
  · intro k
    simpa only [mapW_equiv_val,Equiv.symm_symm] using hh.1 (E k)
  · change varOne (mapW H E.symm) (mapW G E.symm)≤_
    rw [variation_map_equiv]
    exact hh.2

end OneQuill
end
end Lax793645Proofs.Simplifications
