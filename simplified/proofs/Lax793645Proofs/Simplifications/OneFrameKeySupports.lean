import Lax793645Proofs.Simplifications.OneQueryHistograms
import Lax793645Proofs.Simplifications.OneImagePinCaps
import Lax793645Proofs.Simplifications.OnePrimalImageBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Finset
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- A collision on the complete key gives a nonzero common vector
in the primal images at every incident component. -/
theorem one_common_key_primal_intersection (a b : Template p I) (t : Tagging p I)
    (o y : OneUnit p n N) (z z' : Inputs p n I) (m : Mixer p n)
    (hy : ∀ j,oneFrameLaw m (y j))
    (hkey : oneVolleyKeys (a.draw z) t o=oneVolleyKeys (b.draw z') t y)
    (i : I) (e : TagStar (t i)) :
    ¬Disjoint (LinearMap.range (onePrimal (o (a.aim i) e.val)))
      (LinearMap.range (onePrimal (y (b.aim i) e.val))) := by
  intro hd
  have he:=congrFun (congrFun hkey i) e
  change onePrimal _ ((a.draw z).rayAt i)=onePrimal _ ((b.draw z').rayAt i) at he
  have hz:=Submodule.disjoint_def.mp hd _ ⟨_,he⟩ ⟨_,rfl⟩
  have hi:=one_primal_injective (hy (b.aim i)) e.val
  exact point_ne_zero p _ _ (hi (hz.trans (map_zero _).symm))

private theorem disjoint_dual_restrictions {D V : Type} [AddCommGroup D] [Module F D]
    [AddCommGroup V] [Module F V] [FiniteDimensional F D] [Fintype D]
    [Fintype (Module.Dual F V)] (P Q : D→ₗ[F]V) (hP : Function.Injective P)
    (hQ : Function.Injective Q) (h : Disjoint P.range Q.range) (θ : Module.Dual F D) :
    pr unif (fun ξ : Module.Dual F V=>ξ.comp P=0 ∧ ξ.comp Q=θ)=bp (-(2*(dim D:ℝ))) := by
  classical
  let : Fintype (Module.Dual F D):=Fintype.ofInjective
    (fun ξ : Module.Dual F D=>(ξ : D→F)) DFunLike.coe_injective
  let E : Module.Dual F V→ₗ[F](Module.Dual F D × Module.Dual F D):=P.dualMap.prod Q.dualMap
  have hk : (P.coprod Q).ker=⊥ := by
    rw [ker_coprod_of_disjoint_range _ _ h,ker_eq_bot.mpr hP,ker_eq_bot.mpr hQ,Submodule.prod_bot]
  have surj : Function.Surjective E := by
    rintro ⟨u,v⟩
    obtain ⟨ξ,hξ⟩:=LinearMap.dualMap_surjective_of_injective (ker_eq_bot.mp hk) (u.coprod v)
    refine ⟨ξ,Prod.ext ?_ ?_⟩
    · ext x
      simpa [E] using LinearMap.congr_fun hξ (x,0)
    · ext x
      simpa [E] using LinearMap.congr_fun hξ (0,x)
  have htest (ξ : Module.Dual F V) : (ξ.comp P=0 ∧ ξ.comp Q=θ) ↔ E ξ=(0,θ) :=
    by
      change ((E ξ).1=(0,θ).1 ∧ (E ξ).2=(0,θ).2) ↔ _
      exact Prod.ext_iff.symm
  simp_rw [htest]
  change mapW unif E (0,θ)=_
  rw [map_unif_surjective E surj,unif_apply,card_space,bp_neg]
  simp [dim,Module.finrank_prod,Subspace.dual_finrank_eq,two_mul]

/-- A single ambient bit suffices to separate two substantial slices of
the actual raw frame law. On one slice it reads zero on every nominal
point, and on the other it reads one. -/
theorem one_opposite_frame_slices (m : Mixer p n) (e : Comp p.g)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (hsmall : bp (2*num (Row p n)+3-2*(N:ℝ))≤1/2) :
    ∃ ξ : Module.Dual F (Vec (HyperbolicIdx N)),∀ z : F,
      bp (-(2*num (Row p n)+1))≤pr (oneRaw m N) (fun o=>∀ s x,ξ (onePrimal (o e) (point p s x))=z) := by
  classical
  let A:=Module.Dual F (Vec (HyperbolicIdx N))
  let : Fintype A:=Fintype.ofInjective (fun ξ : A=>(ξ : Vec (HyperbolicIdx N)→F))
    DFunLike.coe_injective
  let θ : Module.Dual F (Ray p n):=LinearMap.proj (emptySel,none)
  let P (o : OneOrient p n N):=onePrimal (o e)
  let R (ξ : A) (z : F) (o : OneOrient p n N):=ξ.comp (P o)=z • θ
  let μ:=oneRaw m N
  have law : IsLaw μ:=one_raw_law m hroom
  have valid o (ho : μ o≠0) : Function.Injective (P o) :=
    one_primal_injective (by
      by_contra hn
      exact ho (one_raw_carried m N o hn)) e
  have marg:=product_projection_law (fun _ : Comp p.g=>quadraticChannelRaw
    (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law (quadratic_channel_frames_exist _ (hyperbolic_matrix_nondegenerate N) _
      (one_frame_room hroom))) e
  have sep (y : OneOrient p n N) : (1/2:ℝ)≤pr μ (fun x=>Disjoint (P x).range (P y).range) := by
    have hh:=one_primal_pair_intersection_cap m (y e) hroom hN
    rw [←marg,mapW_pr] at hh
    change pr μ (fun x=>¬Disjoint (P x).range (P y).range)≤_ at hh
    rw [pr_not,law.total] at hh
    linarith only [hh,hsmall]
  let w:=pairW μ μ
  have law' : IsLaw w:=pairW_law law law
  have large : (1/2:ℝ)≤pr w (fun u=>Disjoint (P u.1).range (P u.2).range) := by
    rw [pair_each,←law.avg_const (1/2)]
    exact avg_mono law.nz sep
  let rate:=bp (-(2*num (Row p n)))
  let good (u : OneOrient p n N × OneOrient p n N):=Disjoint (P u.1).range (P u.2).range
  let both (ξ : A) (u : OneOrient p n N × OneOrient p n N):=R ξ 0 u.1 ∧ R ξ 1 u.2
  have freq (u) (hu : w u≠0) (hg : good u) : pr unif (fun ξ : A=>both ξ u)=rate := by
    have hv:=disjoint_dual_restrictions (P u.1) (P u.2) (valid _ (left_ne_zero_of_mul hu))
      (valid _ (right_ne_zero_of_mul hu)) hg θ
    change pr unif (fun ξ : A=>ξ.comp (P u.1)=0 • θ ∧ ξ.comp (P u.2)=1 • θ)=_
    simpa only [zero_smul,one_smul,rate,show dim (Upstream.OAI.HadwigerCounterexample.Ray p n)=
      Fintype.card (Row p n) from dim_vec _,num] using hv
  have hav : rate*pr w good≤avg w (fun u=>pr unif (fun ξ : A=>both ξ u)) := by
    rw [pr,←avg_mul']
    unfold avg
    apply sum_le_sum
    intro u _
    by_cases hu : w u=0
    · simp [hu]
    apply mul_le_mul_of_nonneg_left _ (law'.nz _)
    change rate*ind (good u)≤pr unif (fun ξ : A=>both ξ u)
    by_cases hg : good u
    · rw [ind_one hg,mul_one,freq u hu hg]
    rw [ind_zero hg,mul_zero]
    exact pr_nonneg (unif_law (α:=A)).nz
  have hs : bp (-(2*num (Row p n)+1))≤avg unif (fun ξ : A=>pr μ (R ξ 0)*pr μ (R ξ 1)) := by
    calc
      _ = rate*(1/2:ℝ) := by
        unfold rate
        rw [neg_add, bp_add, bp_neg 1, bp_one]
        ring
      _ ≤ rate*pr w good := mul_le_mul_of_nonneg_left large (bp_pos _).le
      _ ≤ _ := hav.trans_eq (by
        unfold pr
        rw [avg_avg]
        apply avg_congr
        intro ξ _
        exact pairW_pr μ μ (R ξ 0) (R ξ 1))
  obtain ⟨ξ,_,hmax⟩:=Finset.exists_max_image (univ : Finset A)
    (fun ξ=>pr μ (R ξ 0)*pr μ (R ξ 1)) univ_nonempty
  have hξ:=hs.trans ((unif_law (α:=A)).avg_le (fun j=>hmax j (mem_univ _)))
  refine ⟨ξ,fun z=>?_⟩
  have hz : bp (-(2*num (Row p n)+1))≤pr μ (R ξ z) := by
    rcases bit_cases z with rfl|rfl
    · exact hξ.trans (mul_le_of_le_one_right (pr_nonneg law.nz) ((pr_le_tot law.nz).trans law.total.le))
    · exact hξ.trans (mul_le_of_le_one_left (pr_nonneg law.nz) ((pr_le_tot law.nz).trans law.total.le))
  refine hz.trans (pr_mono law.nz ?_)
  intro o ho s x
  have he:=LinearMap.congr_fun ho (point p s x)
  simpa only [LinearMap.comp_apply,LinearMap.smul_apply,θ,LinearMap.proj_apply,point_base_eval,baseV,
    Option.elim'_none,smul_eq_mul,mul_one] using he

private theorem all_frame_slices (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (hsmall : bp (2*num (Row p n)+3-2*(N:ℝ))≤1/2) :
    ∃ ξ : Comp p.g→Module.Dual F (Vec (HyperbolicIdx N)),∀ z : F,
      bp (-((2*num (Row p n)+1)*num (Comp p.g)))≤pr (oneRaw m N)
        (fun o=>∀ e s x,ξ e (onePrimal (o e) (point p s x))=z) := by
  classical
  choose ξ hξ using fun e : Comp p.g=>one_opposite_frame_slices m e hroom hN hsmall
  refine ⟨ξ,fun z=>?_⟩
  let μ:=quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
    (selfM p n m.mixM).toQuadraticForm'
  let R (e : Comp p.g) (f : OneFrame p n N):=∀ s x,ξ e (onePrimal f (point p s x))=z
  have law : IsLaw μ:=unifOn_law (quadratic_channel_frames_exist _ (hyperbolic_matrix_nondegenerate N)
    _ (one_frame_room hroom))
  let c:=bp (-(2*num (Row p n)+1))
  have bound e : c≤pr μ (R e) := by
    have hm:=product_projection_law (fun _ : Comp p.g=>μ) (fun _=>law) e
    calc
      c≤pr (oneRaw m N) (fun o=>R e (o e)) := hξ e z
      _ = pr (mapW (oneRaw m N) (fun o=>o e)) (R e) := (mapW_pr ..).symm
      _ = pr μ (R e) := congrArg (fun w=>pr w (R e)) hm
  change _≤pr (prodW (fun _ : Comp p.g=>μ)) (fun o=>∀ e,R e (o e))
  rw [prodW_pr]
  calc
    _ = ∏ _e : Comp p.g,c := by simp only [prod_const,card_univ,c,←bp_mul_nat,num]; congr 1; ring
    _ ≤ _ := Finset.prod_le_prod (fun _ _=>(bp_pos _).le) (fun e _=>bound e)

/-- No complete key of an option with a nonempty list at each cross edge
can occur on both sides, even before imposing its script or statuses. -/
def NoSharedOption (U V : Wgt (OneUnit p n N)) : Prop :=
  ∀ u v,U u≠0 → V v≠0 → ∀ {q : StatusAnalysis.Format} {d e : StatusAnalysis.Rates}
    (x : StatusAnalysis.Typus p q d e), (∀ j,1≤q j) →
    ∀ z z' : Inputs p n (StatusAnalysis.Messenger q),
      oneVolleyKeys ((x.qA.pen x.t).draw z) x.t u ≠ oneVolleyKeys ((x.qB.pen x.t).draw z') x.t v

private theorem histogram_key_witness {A O T : Type} [Fintype A] [Fintype O] [Fintype T]
    (key : A→O→T) (w : Wgt O) (μ : Wgt A) (P : A→O→Prop) (k : T)
    (h : inputHistogram key w μ P k≠0) : ∃ a o,w o≠0 ∧ key a o=k := by
  classical
  change (∑ a,μ a*pr w (fun o=>P a o ∧ key a o=k))≠0 at h
  obtain ⟨a,_,ha⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
  have he:=right_ne_zero_of_mul ha
  change (∑ o,w o*ind (P a o ∧ key a o=k))≠0 at he
  obtain ⟨o,_,ho⟩:=Finset.exists_ne_zero_of_sum_ne_zero he
  refine ⟨a,o,left_ne_zero_of_mul ho,?_⟩
  by_contra hn
  exact (right_ne_zero_of_mul ho) (ind_zero fun h=>hn h.2)

/-- For opposite laws the actual accepted measures have zero overlap
for every complete option and every choice of acceptance filters. -/
theorem NoSharedOption.zero_overlap {U V : Wgt (OneUnit p n N)} (h : NoSharedOption U V)
    {q : StatusAnalysis.Format} {d e : StatusAnalysis.Rates} (x : StatusAnalysis.Typus p q d e)
    (hq : ∀ j,1≤q j) (ν : Wgt (OneKeys x.t N)) (μ π : Wgt (Inputs p n (StatusAnalysis.Messenger q)))
    (P Q : Inputs p n (StatusAnalysis.Messenger q)→OneUnit p n N→Prop) :
    overlap ν (oneHistogram (x.qA.pen x.t).draw x.t U μ P) (oneHistogram (x.qB.pen x.t).draw x.t V π Q)=0 := by
  classical
  unfold overlap avg
  apply sum_eq_zero
  intro k _
  by_cases hA : oneHistogram (x.qA.pen x.t).draw x.t U μ P k=0
  · simp [density,hA]
  have hB : oneHistogram (x.qB.pen x.t).draw x.t V π Q k=0 := by
    by_contra hB
    obtain ⟨z,u,hu,hu'⟩:=histogram_key_witness _ _ _ _ _ hA
    obtain ⟨z',v,hv,hv'⟩:=histogram_key_witness _ _ _ _ _ hB
    exact h u v hu hv x hq z z' (hu'.trans hv'.symm)
  simp [density,hB]

/-- The two laws have equal endpoint marginals, obey exponential raw
density bounds and require opposite two-endpoint key relations. -/
def OppositeKeyLaws (m : Mixer p n) (N : ℕ) (cap : ℝ)
    (each : Wgt (OneUnit p n N)→Prop) : Prop :=
    ∃ U V : Wgt (OneUnit p n N),IsLaw U ∧ IsLaw V ∧
      (∀ i : Bool,mapW U (fun o=>o i)=mapW V (fun o=>o i)) ∧
      (∀ o, U o≤cap*oneUnitRaw m N o ∧ V o≤cap*oneUnitRaw m N o) ∧ each U ∧ each V ∧
      NoSharedOption U V ∧ NoSharedOption V V

/-- Two capped laws of actual units with the same endpoint marginals.
No supported pair can match the full keys of any option with nonempty lists. -/
theorem one_capped_opposite_keys (m : Mixer p n) (hg : 2≤p.g)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (hsmall : bp (2*num (Row p n)+3-2*(N:ℝ))≤1/2) :
    OppositeKeyLaws m N (bp ((4*num (Row p n)+2)*num (Comp p.g))) (fun _=>True) := by
  classical
  obtain ⟨ξ,hξ⟩:=all_frame_slices m hroom hN hsmall
  let R (z : F) (o : OneOrient p n N) := ∀ e s x,ξ e (onePrimal (o e) (point p s x))=z
  let σ (z : F):=onW (oneRaw m N) (R z)
  have law:=one_raw_law m hroom
  have hσ (z : F) : IsLaw (σ z):=on_law law.nz ((bp_pos _).trans_le (hξ z))
  let color (a z : F) (i : Bool) := if i then z else z+a
  let prod (a z : F) : Wgt (OneUnit p n N):=prodW (fun i : Bool=>σ (color a z i))
  let W (a : F) : Wgt (OneUnit p n N):=mixW unif (prod a)
  have lawW (a : F) : IsLaw (W a):=mixW_law unif_law (fun z=>prodW_law (fun i=>hσ _))
  have marg (a : F) (i : Bool) (f : Wgt (OneOrient p n N)) :
      avg (mapW (W a) (fun o=>o i)) f=avg unif (fun z : F=>avg (σ (color a z i)) f) := by
    rw [mapW_avg]
    change avg (mixW unif (prod a)) _=_
    rw [mixW_avg]
    apply avg_congr
    intro z _
    exact ((mapW_avg (prod a z) (fun o=>o i) f).symm.trans
      (congrArg (fun v=>avg v f) (product_projection_law (fun j=>σ (color a z j)) (fun _=>hσ _) i)))
  have common (i : Bool) : mapW (W 0) (fun o=>o i)=mapW (W 1) (fun o=>o i) := by
    apply weights_eq_of_tests
    intro f
    rw [marg,marg]
    cases i
    · simp only [color,Bool.false_eq_true,if_false,add_zero]
      exact (avg_bij (Equiv.addRight (1:F)) unif (fun z=>avg (σ z) f)).symm
    · rfl
  let C:=bp ((2*num (Row p n)+1)*num (Comp p.g))
  have cap (z : F) (o) : σ z o≤C*oneRaw m N o := by
    simpa only [C,bp_neg,inv_inv] using on_mon law.nz (bp_pos _) (hξ z) o
  have capW (a : F) (o) : W a o≤bp ((4*num (Row p n)+2)*num (Comp p.g))*oneUnitRaw m N o := by
    change avg unif (fun z : F=>prod a z o)≤_
    rw [←(unif_law (α:=F)).avg_const (bp ((4*num (Row p n)+2)*num (Comp p.g))*oneUnitRaw m N o)]
    apply avg_mono unif_law.nz
    intro z
    simp only [prod,oneUnitRaw,prodW,Fintype.prod_bool]
    refine (mul_le_mul (cap _ _) (cap _ _) ((hσ _).nz _) (mul_nonneg (bp_pos _).le (law.nz _))).trans_eq ?_
    rw [show bp ((4*num (Row p n)+2)*num (Comp p.g))=C*C by unfold C; rw [←bp_add]; congr 1; ring]
    ring
  have support (a : F) (o) (ho : W a o≠0) : ∃ z : F,∀ i,R (color a z i) (o i) := by
    change ∑ z : F,unif z*prod a z o≠0 at ho
    obtain ⟨z,_,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero ho
    have hp : prod a z o≠0:=right_ne_zero_of_mul hz
    exact ⟨z,fun i=>(onW_ne (Finset.prod_ne_zero_iff.mp hp i (mem_univ i))).1⟩
  have avoid (a : F) : NoSharedOption (W a) (W 1) := by
    intro u v hu hv q d d' x hq zA zB heq
    obtain ⟨z,hz⟩:=support a u hu
    obtain ⟨z',hz'⟩:=support 1 v hv
    let pos (i : Bool) : StatusAnalysis.Messenger q:=⟨(true,i),⟨0,hq _⟩⟩
    have he (i : Bool) : color a z true=color 1 z' i := by
      let j:=pos i
      obtain ⟨e⟩ : Nonempty (TagStar (x.t j)) :=
        Fintype.card_pos_iff.mp ((card_star (x.t j)).symm ▸ tagDegree_pos hg)
      have hkey:=congrFun (congrFun heq j) e
      exact (hz true e.val _ _).symm.trans ((congrArg (ξ e.val) hkey).trans (hz' i e.val _ _))
    have h0:=he false
    have h1:=he true
    change z=z'+1 at h0
    change z=z' at h1
    simp [h1] at h0
  exact ⟨W 0,W 1,lawW 0,lawW 1,common,fun o=>⟨capW _ o,capW _ o⟩,trivial,trivial,avoid 0,avoid 1⟩

private theorem tilted_image_spreading (m : Mixer p n) {ε : ℝ} (hε : 0<ε) (hε' : ε≤1)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hroom : (dim (OneFull p n):ℝ)+2≤((ε/2)/6)*(2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w)
    (hc : ∀ o,w o≤bp (ε*N)*oneUnitRaw m N o)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N)) :
    pr w (imagePinAgree oneCoordinateImages a)≤fee (2*N) ε (imagePlanRank a.sp) := by
  by_cases hz : imagePlanRank a.sp=0
  · simpa only [hz,fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero,hw.total] using
      (pr_le_tot (p:=imagePinAgree oneCoordinateImages a) hw.nz)
  have ht : (1:ℝ)≤ imagePlanRank a.sp:=by exact_mod_cast (show 1≤ imagePlanRank a.sp by omega)
  have hraw:=one_image_pin_cap m a (ζ:=ε/2) (by positivity) (by linarith) hN hroom
  refine (pr_cap hc _).trans ((mul_le_mul_of_nonneg_left hraw (bp_pos _).le).trans ?_)
  unfold fee
  rw [←bp_add]
  apply bp_le
  push_cast
  have h:=mul_le_mul_of_nonneg_left ht (show 0≤ε*N by positivity)
  nlinarith only [h]

/-- For every positive spreading allowance at most one, there are opposite
key laws within that density allowance. Both laws also satisfy spreading
on every exact image test, for every mixer in the resulting dimensions. -/
theorem one_capped_opposite_keys_calendar (p : Shape) (hg : 2≤p.g) (ε : ℝ) (hε : 0<ε) (hε' : ε≤1) :
    ∀ᶠ M : ℕ in atTop,∀ n : ℕ,1≤n → ∀ m : Mixer p n,
      OppositeKeyLaws m (M*n) (bp (ε*((M*n:ℕ):ℝ))) (fun w=>∀ a,
        pr w (imagePinAgree oneCoordinateImages a)≤fee (2*(M*n)) ε (imagePlanRank a.sp)) := by
  filter_upwards [columns_budget p (δ:=1) zero_lt_one 4 5 (by norm_num) (by norm_num),
    columns_budget p hε (4*num (Comp p.g)) (2*num (Comp p.g))
      (by unfold num; positivity) (by unfold num; positivity),
    columns_budget p (δ:=ε/12) (by positivity) 4 5 (by norm_num) (by norm_num)]
    with M hcols hcap heval n hn m
  have hc:=hcols n hn
  rw [one_mul,show num (Full p n)=num (Row p n)+p.h by simp [num,Full]] at hc
  have hrow : 0≤num (Row p n):=by unfold num; positivity
  have hh : (0:ℝ)≤p.h:=Nat.cast_nonneg _
  have hroom : num (Row p n)+2*p.h+1≤((M*n:ℕ):ℝ):=by linarith only [hc,hrow,hh]
  have hN : (5:ℝ)≤((M*n:ℕ):ℝ):=by linarith only [hc,hrow,hh]
  have hsmall : bp (2*num (Row p n)+3-2*((M*n:ℕ):ℝ))≤1/2 := by
    rw [show (1/2:ℝ)=bp (-1) by rw [bp_neg,bp_one]; norm_num]
    apply bp_le
    linarith only [hc,hrow,hh]
  obtain ⟨U,V,hU,hV,hm,hc',_,_,hs⟩:=one_capped_opposite_keys m hg (by exact_mod_cast hroom)
    (by exact_mod_cast hN) hsmall
  have ht:=hcap n hn
  rw [show num (Full p n)=num (Row p n)+p.h by simp [num,Full]] at ht
  have hc'' : bp ((4*num (Row p n)+2)*num (Comp p.g))≤bp (ε*((M*n:ℕ):ℝ)):=bp_le (by
    have hcg : 0≤num (Comp p.g):=by unfold num; positivity
    nlinarith only [ht,mul_nonneg hcg hh])
  have raw:=one_unit_raw_law m (by exact_mod_cast hroom)
  have cap (o) := mul_le_mul_of_nonneg_right hc'' (raw.nz o)
  have capU o:=(hc' o).1.trans (cap o)
  have capV o:=(hc' o).2.trans (cap o)
  have hdim : 2*dim (OneFull p n)+3≤M*n := by
    rw [one_full_dimension]
    have ht : 2*(num (Row p n)+2*p.h)+3≤((M*n:ℕ):ℝ):=by linarith only [hc,hrow]
    exact_mod_cast ht
  have hr : (dim (OneFull p n):ℝ)+2≤((ε/2)/6)*(2*((M*n:ℕ):ℝ)) := by
    have heval:=heval n hn
    rw [show num (Full p n)=num (Row p n)+p.h by simp [num,Full]] at heval
    rw [one_full_dimension]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change num (Row p n)+2*p.h+2≤_
    push_cast at heval
    nlinarith only [heval,hrow,hh,mul_nonneg hε.le
      (show (0:ℝ)≤(M:ℝ)*n by positivity)]
  exact ⟨U,V,hU,hV,hm,fun o=>⟨capU o,capV o⟩,
    tilted_image_spreading m hε hε' hdim hr U hU capU,
    tilted_image_spreading m hε hε' hdim hr V hV capV,hs⟩

/-- Even two independent draws from a single spreading unit law can
give zero overlap for every full option. The prepared mixed endpoint
assumptions of the graph theorem are stronger than this law's cap. -/
theorem one_spreading_zero_overlap (p : Shape) (hg : 2≤p.g) (ε : ℝ) (hε : 0<ε) (hε' : ε≤1) :
    ∀ᶠ M : ℕ in atTop,∀ n : ℕ,1≤n → ∀ m : Mixer p n,
      ∃ W : Wgt (OneUnit p n (M*n)),IsLaw W ∧ (∀ o,W o≤bp (ε*((M*n:ℕ):ℝ))*oneUnitRaw m (M*n) o) ∧
        (∀ a,pr W (imagePinAgree oneCoordinateImages a)≤fee (2*(M*n)) ε (imagePlanRank a.sp)) ∧
        ∀ {q : StatusAnalysis.Format} {d e : StatusAnalysis.Rates} (x : StatusAnalysis.Typus p q d e),
          (∀ j,1≤q j) → ∀ (ν : Wgt (OneKeys x.t (M*n))) (μ π : Wgt (Inputs p n (StatusAnalysis.Messenger q)))
            (P Q : Inputs p n (StatusAnalysis.Messenger q)→OneUnit p n (M*n)→Prop),
          overlap ν (oneHistogram (x.qA.pen x.t).draw x.t W μ P)
            (oneHistogram (x.qB.pen x.t).draw x.t W π Q)=0 := by
  filter_upwards [one_capped_opposite_keys_calendar p hg ε hε hε'] with M h n hn m
  obtain ⟨_,W,_,law,_,cap,_,spread,_,hW⟩:=h n hn m
  exact ⟨W,law,fun o=>(cap o).2,spread,fun x hx=>hW.zero_overlap x hx⟩

end
end Lax793645Proofs.Simplifications
