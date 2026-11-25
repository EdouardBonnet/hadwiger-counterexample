import Lax793645Proofs.Simplifications.OneStableScalarOptions
import Lax793645Proofs.Simplifications.GenericStatusSpans

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function LinearMap Finset Matrix Submodule
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N r K c R : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}

set_option maxHeartbeats 900000 in
theorem generic_plenitude_at_budget (budget : ℕ) (h:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (hg:3 ≤ p.g) (A B:Stalls p) (hk : ∀ i,(A i).card+budget < Fintype.card (Label p.b))
    (hl : ∀ i,(B i).card+budget < Fintype.card (Label p.b))
    (hβ:0<β) (hz:0<η) (hη : playbook p K*η<1/2*β^2)
    (hd:∀ i,d i≤K^2) (he:∀ i,e i≤K^2):
    richAt (genericStellar u s t η A B) budget := by
  classical
  intro i S hu y
  have hh a (b:Finset (Label p.b)) (h : b.card+budget<Fintype.card (Label p.b)):
      ∃ z,z∉b∧z∉S a := by
    obtain ⟨z,hz⟩:=any_label (b∪S a) ((card_union_le ..).trans_lt ((Nat.add_le_add_left
      (hu a) _).trans_lt h))
    exact ⟨z,fun ht=>hz (mem_union_left _ ht),fun ht=>hz (mem_union_right _ ht)⟩
  obtain ⟨v,h1,h2⟩:= hh true (A i.1) (hk _)
  obtain ⟨w,h3,h4⟩:= hh false (B i.2) (hl _)
  let x : Zodiac p:= ⟨⟨0,by omega⟩,y.1,fun i=>if i then v else w,fun _=>Flavor.full⟩
  have hh : x.common:= fun i=> generic_apt p hg _ rfl
  obtain ⟨W,hA,hB,hC⟩:= sturdy_contact u s t h hs ht hβ x hh (fun _=>rfl) i y.2.1 y.2.2 hz
    ((mul_le_mul_of_nonneg_right (booklet_cap p K _ _ (hd _) (he _)) hz.le).trans_lt hη)
  refine ⟨(x,W),⟨⟨⟨h1,h3,hA⟩,fun _=>rfl⟩,fun i=>?_⟩,?_⟩
  · cases i; exact h4; exact h2
  exact Prod.ext rfl (Prod.ext hB hC)
set_option maxHeartbeats 1000000 in
/-- Enumeration as a numerical option preserves the full selector
independence, not only distinctness of the labels. -/
theorem generic_independent_invite (p : Shape) (u : Terrain p r)
    (s : Gazette p r d) (t : Gazette p r e) (A B : Stalls p) (η : ℝ)
    (U : Bool → Space (Vec (SelIdx p.b p.j))) (v : ∀ i,Suite d e i)
    (H : Straps (Label p.b)) (f : Bags (Scriptum p d e))
    (hf : IndependentParade (genericStellar u s t η A B) U H v f Finset.univ) :
    let C := genericStellar u s t η A B
    ∃ (q : Volumes) (g : Engagement p (toFormat q) d e),
      (∀ i,1 ≤ toFormat q i ∧ toFormat q i ≤ 7) ∧
      (∀ i : Messenger (toFormat q),(C i.1).valid (g i)) ∧
      (∀ side : Bool,LinearIndependent F
        ((U side).mkQ ∘ fun i : Messenger (toFormat q) => selV p.j ((g i).1.s side))) ∧
      ∀ i,∑ j : Fin (toFormat q i),(C i).writes (g ⟨i,j⟩)=v i := by
  classical
  intro C
  have he i := hf.batch i (mem_univ _)
  let q (i : Grid) : Fin 8 := ⟨(f i).card,Nat.lt_succ_of_le (he i).2.2.2⟩
  let Q := toFormat q
  let E (i : Grid) : Fin (Q i) ≃ (↑(f i) : Type) :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let g : Engagement p Q d e := fun i => (E _ i.2).val
  have hG i : g i ∈ f i.1 := (E i.1 i.2).property
  let embed (i : Messenger Q) :
      (Finset.univ.sigma f : Set (Σ k,Scriptum p d e k)) :=
    ⟨⟨i.1,g i⟩,Finset.mem_sigma.mpr ⟨Finset.mem_univ _,hG i⟩⟩
  have hinj : Injective embed := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i=j := congrArg (fun z => z.val.1) h
    subst j
    have hval : (E i x).val=(E i y).val :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
    have hxy : x=y := (E i).injective (Subtype.ext hval)
    subst y
    rfl
  refine ⟨q,g,fun i => (he i).2.2,fun i => ((he _).1.1 _ (hG i)).1,
    fun side => ?_,fun i => ?_⟩
  · exact (hf.independent side).comp embed hinj
  calc _ = ∑ x : ↑(f i),(C i).writes x.val :=
          Equiv.sum_comp (E i) (fun x => (C i).writes x.val)
       _ = _ := (Finset.sum_coe_sort (f i) _).trans (he i).2.1
set_option maxHeartbeats 1400000 in
/-- The strengthened scalar lists produce actual admissible numerical
options. Their protection is independent of the subsequently sampled inputs. -/
theorem one_generic_processions {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
    (A B : Stalls p) (η : ℝ) (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (X : Charts p n d) (W : Charts p n e) (T : OneCross p n)
    (hA : oneCharted X a.sp) (hB : oneCharted W b.sp)
    (ha : oneTableSafe a.sp b.sp T) (hb : oneTableSafe b.sp a.sp (fun e=>(T e)ᵀ))
    (Pa : OnePlanProtection a.sp K)
    (Pb : OnePlanProtection b.sp K)
    (hg : 3 ≤ p.g) (hodd : Odd p.g) (hp : 1 ≤ p.J) (H : Straps (Label p.b))
    (hsupply : ∀ target : ∀ i,Suite d e i,
      (∀ i,target i ∈ chapter (genericStellar u s t η A B) H i) →
      ∃ f,IndependentParade (genericStellar u s t η A B)
        (fun side => if side then Pa.selector else Pb.selector) H target f Finset.univ)
    (hv : scorecard (chapter (genericStellar u s t η A B) H) (oneHailing X W T)) :
    ∃ (q : Volumes) (g : Engagement p (toFormat q) d e)
      (s0 t0 : Script p (Messenger (toFormat q))),
      OneOptions.chances (g.binding p s0 t0) X W a b T K ∧
        (∀ i : Messenger (toFormat q),η ≤ circlet u s t (g i).1 i.1 (g i).2) ∧
        ∀ i : Messenger (toFormat q),∀ side,(g i).1.f side=Flavor.full := by
  classical
  obtain ⟨target,htarget,hscalar⟩ := hv
  obtain ⟨f,hf⟩ := hsupply target htarget
  obtain ⟨q,g,hI,hG0,hLI,hQ⟩ := generic_independent_invite p u s t A B η _ target H f hf
  have hG i := (hG0 i).1
  have hS (side : Bool) : Injective (fun i : Messenger (toFormat q) => (g i).1.s side) := by
    intro i j hij
    change (g i).1.s side=(g j).1.s side at hij
    apply (hLI side).injective
    change (if side then Pa.selector else Pb.selector).mkQ (selV p.j ((g i).1.s side))=
      (if side then Pa.selector else Pb.selector).mkQ (selV p.j ((g j).1.s side))
    rw [hij]
  let z := g.tags p
  let w := g.bits p
  let F0 := g.genre0 p
  let F1 := g.genre1 p
  have hM : F0.up z w ∧ F1.up z w := by
    constructor
    · exact ⟨hS true,fun i => (hG i).2.2.2.1.2.1,fun i => (hG i).2.2.2.1.1⟩
    exact ⟨hS false,fun i => (hG i).2.2.2.2.1.2.1,fun i => (hG i).2.2.2.2.1.1⟩
  have hPa : OnePenSpace ((F0.hang 0).pen z) a.sp K :=
    Pa.protect_template _ (one_messenger_card (p:=p) (n:=n) hI) (hLI true)
  have hPb : OnePenSpace ((F1.hang 0).pen z) b.sp K :=
    Pb.protect_template _ (one_messenger_card (p:=p) (n:=n) hI) (hLI false)
  obtain ⟨P,Q,hP⟩ := OneOptions.optionVia (toFormat q) d e a b T K ha hb z X W hA hB F0 F1
    hPa hPb w hM.1 hM.2 hp hg hodd hI (by
      have he : sendSum w F0.amp F1.amp=target := funext (fun i => hQ i)
      rw [he]
      exact hscalar)
  exact ⟨q,g,P,Q,hP,(fun i => (hG i).2.2.2.2.2),fun i=>(hG0 i).2⟩
/-- The seven-generator construction starts from the original spans.
Polynomial continuation supplies all later deletion invariance. -/
theorem one_generic_scalar_options
    (hu : origami p r u δ) (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hg : 3≤p.g) (hodd : Odd p.g) (hj : 1≤p.j) (hJ : 1≤p.J)
    (hlabels : 9*oneScalarBudget p K<Fintype.card (Label p.b))
    (hβ : 0<β) (hη : 0<η) (hsmall : playbook p K*η<1/2*β^2)
    (hd : ∀ i,d i≤K^2) (he : ∀ i,e i≤K^2)
    (hstable : ∀ i,∀ S : Straps (Label p.b),(∀ side,(S side).card≤oneScalarBudget p K)→
      (genericStellar u s t η ⊥ ⊥ i).band S=(stellar u s t η ⊥ ⊥ i).band ⊥)
    (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (haK : imagePlanRank a.sp≤K) (hbK : imagePlanRank b.sp≤K)
    (X : Charts p n d) (W : Charts p n e) (T : OneCross p n)
    (hA : oneCharted X a.sp) (hB : oneCharted W b.sp)
    (ha : oneTableSafe a.sp b.sp T) (hb : oneTableSafe b.sp a.sp (fun e=>(T e)ᵀ)) :
    scorecard (chapter (stellar u s t η ⊥ ⊥) ⊥) (oneHailing X W T)→
      ∃ (q : Volumes) (g : Engagement p (toFormat q) d e)
        (s0 t0 : Script p (Messenger (toFormat q))),
        OneOptions.chances (g.binding p s0 t0) X W a b T K ∧
          (∀ i : Messenger (toFormat q),η≤circlet u s t (g i).1 i.1 (g i).2) ∧
            ∀ i : Messenger (toFormat q),∀ side,(g i).1.f side=Flavor.full := by
  classical
  obtain ⟨Pa⟩:=one_plan_protection_exists a.sp K (fun e=>(image_plan_component_dimension _ e).trans haK)
  obtain ⟨Pb⟩:=one_plan_protection_exists b.sp K (fun e=>(image_plan_component_dimension _ e).trans hbK)
  let U (side : Bool):=if side then Pa.selector else Pb.selector
  let D:=oneSelectorProtectionDim p K
  let C:=genericStellar u s t η ⊥ ⊥
  have hU (side : Bool) : dim (U side)≤D := by
    cases side
    · exact Pb.selector_dim
    exact Pa.selector_dim
  have hlabels' (i : Nodes) : ((⊥ : Stalls p) i).card+9*oneScalarBudget p K<
      Fintype.card (Label p.b) := by simpa using hlabels
  have hrich:=generic_plenitude_at_budget (9*oneScalarBudget p K) hu hs ht hg ⊥ ⊥
    hlabels' hlabels' hβ hη hsmall hd he
  have hsupply (target : ∀ i,Suite d e i) (htarget : ∀ i,target i∈chapter C ⊥ i) :
      ∃ g,IndependentParade C U ⊥ target g Finset.univ := by
    apply independent_parade_of_stability C hj U D hU ⊥ (chapter C ⊥) ?_ ?_ target htarget
    · intro i S hS
      have hzero:=hstable i ⊥ (fun _=>by simp)
      simpa only [bot_sup_eq,C,chapter] using (hstable i S hS).trans hzero.symm
    · intro i S hS y
      have hsize (side) : (S side).card≤9*oneScalarBudget p K := by
        have hh:=hS side
        change (S side).card≤oneScalarBudget p K at hh
        omega
      simpa only [bot_sup_eq] using hrich i S hsize y
  intro hv
  have hchap : chapter C ⊥=chapter (stellar u s t η ⊥ ⊥) ⊥ := by
    funext i
    exact hstable i ⊥ (fun _=>by simp)
  rw [←hchap] at hv
  exact one_generic_processions ⊥ ⊥ η a b X W T hA hB ha hb Pa Pb
    hg hodd hJ ⊥ hsupply hv

end
end Lax793645Proofs.Simplifications
