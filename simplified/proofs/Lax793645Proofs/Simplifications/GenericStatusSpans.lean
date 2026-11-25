import Lax793645Proofs.Simplifications.ExactSupportSpanStability

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

def GenericStatusPrediction (u : Terrain p r) (s : Gazette p r d)
    (i : Nodes) (A : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p r) : Prop :=
  ∀ x : Appearance p,x.s∉A→x.apt→x.f=Flavor.full→∀ c,0<u x.l x.q c→
    ∀ v,0<s i x c v→a.soot x v=f x.l x.q c

theorem generic_status_predictors
    (hs : ∀ i (x : Appearance p),x.apt→∀ c,IsLaw (s i x c))
    (ht : ∀ i (x : Appearance p),x.apt→∀ c,IsLaw (t i x c))
    (i : Grid) (A B : Finset (Label p.b))
    (hA : A.card<Fintype.card (Label p.b)) (hB : B.card<Fintype.card (Label p.b))
    (hg : 3≤p.g) (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2))
    (h : ∀ x y : Appearance p,x.s∉A→y.s∉B→x.apt→y.apt→x.f=Flavor.full→y.f=Flavor.full→x.l=y.l→x.q=y.q→
      ∀ c,0<u x.l x.q c→∀ v w,0<s i.1 x c v→0<t i.2 y c w→a.soot x v=b.soot y w) :
    ∃ f : Pulsar p r,GenericStatusPrediction u s i.1 A a f ∧
      GenericStatusPrediction u t i.2 B b f := by
  classical
  obtain ⟨a₀,ha₀⟩:=any_label A hA
  obtain ⟨b₀,hb₀⟩:=any_label B hB
  let Left (l : Tag p.g) (q : F):=
    {x : Appearance p // x.l=l ∧ x.q=q ∧ x.s∉A ∧ x.apt ∧ x.f=Flavor.full}
  let Right (l : Tag p.g) (q : F):=
    {x : Appearance p // x.l=l ∧ x.q=q ∧ x.s∉B ∧ x.apt ∧ x.f=Flavor.full}
  have choice (l : Tag p.g) (q : F) : ∃ φ : Fin r→F,
      (∀ c,0<u l q c→∀ x : Left l q,∀ v,0<s i.1 x.val c v→a.soot x.val v=φ c) ∧
      (∀ c,0<u l q c→∀ y : Right l q,∀ w,0<t i.2 y.val c w→b.soot y.val w=φ c) := by
    let : Nonempty (Left l q):=
      ⟨⟨amazes p a₀ l q,rfl,rfl,ha₀,generic_apt p hg _ rfl,rfl⟩⟩
    let : Nonempty (Right l q):=
      ⟨⟨amazes p b₀ l q,rfl,rfl,hb₀,generic_apt p hg _ rfl,rfl⟩⟩
    apply exact_family_predictor
      (fun x : Left l q=>s i.1 x.val) (fun y : Right l q=>t i.2 y.val)
      (fun x c=>hs i.1 x.val x.property.2.2.2.1 c)
      (fun y c=>ht i.2 y.val y.property.2.2.2.1 c)
      (fun x=>a.soot x.val) (fun y=>b.soot y.val) (fun c=>0<u l q c)
    intro c hc x y v w hv hw
    apply h x.val y.val x.property.2.2.1 y.property.2.2.1
      x.property.2.2.2.1 y.property.2.2.2.1
      x.property.2.2.2.2 y.property.2.2.2.2
      (x.property.1.trans y.property.1.symm) (x.property.2.1.trans y.property.2.1.symm) c
    · simpa only [x.property.1,x.property.2.1] using hc
    · exact hv
    · exact hw
  choose f hf hf' using choice
  refine ⟨f,?_,?_⟩
  · intro x hx hapt hfull c hc v hv
    exact hf x.l x.q c hc ⟨x,rfl,rfl,hx,hapt,hfull⟩ v hv
  · intro y hy hapt hfull c hc w hw
    exact hf' y.l y.q c hc ⟨y,rfl,rfl,hy,hapt,hfull⟩ w hw
def GenericStatusContinuation (u : Terrain p r) (s : Gazette p r d) (B : ℕ) : Prop :=
  ∀ i E,E.card≤B→∀ a f,GenericStatusPrediction u s i E a f→
    ExactStatusPrediction u s i ∅ a f

def genericStellar (u : Terrain p r) (s : Gazette p r d) (t : Gazette p r e)
    (η : ℝ) (A B : Stalls p) : Congress (Scriptum p d e) d e (Label p.b) :=
  fun i=>{stellar u s t η A B i with
    valid x:=(stellar u s t η A B i).valid x ∧ ∀ side,x.1.f side=Flavor.full}

theorem generic_status_band_stable (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η) (hη : 0<η) (hg : 3≤p.g)
    (B : ℕ) (hB : B<Fintype.card (Label p.b))
    (hleft : GenericStatusContinuation u s B) (hright : GenericStatusContinuation u t B)
    (S : Straps (Label p.b)) (hS : ∀ side,(S side).card≤B) (i : Grid) :
    (genericStellar u s t η ⊥ ⊥ i).band S=(stellar u s t η ⊥ ⊥ i).band ⊥ := by
  classical
  let C:=genericStellar u s t η ⊥ ⊥ i
  let C0:=stellar u s t η ⊥ ⊥ i
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨v,hv,rfl⟩
    exact C0.band_write ⊥ ⟨hv.1.1,fun _=>by simp⟩
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (C.band S) (C0.writes v)).mp
  intro f hf
  have hf' := (Submodule.mem_dualAnnihilator f).mp hf
  obtain ⟨a,b,hab⟩:=signal_rhyme_form f
  have hrel (x y : Appearance p) (hx : x.s∉S true) (hy : y.s∉S false)
      (hax : x.apt) (hay : y.apt) (hfullx : x.f=Flavor.full) (hfully : y.f=Flavor.full) (hl : x.l=y.l) (hq : x.q=y.q)
      (c : Fin r) (hc : 0<u x.l x.q c)
      (z : Magazine p (d i.1)) (w : Magazine p (e i.2))
      (hz : 0<s i.1 x c z) (hw : 0<t i.2 y c w) : a.soot x z=b.soot y w := by
    let X:=amends p x y
    have he : X.aspect false=y:=amendsB x y hl hq
    have hcommon : X.common := by
      intro side
      cases side
      · rw [he]; exact hay
      exact hax
    have hpos : 0<circlet u s t X i (z,w) := by
      have hnonneg (j : Fin r) : 0≤u X.l X.q j*
          (s i.1 (X.aspect true) j z*t i.2 (X.aspect false) j w) :=
        mul_nonneg ((hu.1 _ _).nz j) (mul_nonneg ((hs.law _ _ (hcommon true) j).nz z)
          ((ht.law _ _ (hcommon false) j).nz w))
      apply (mul_pos hc (mul_pos hz (show 0<t i.2 (X.aspect false) c w by rw [he]; exact hw))).trans_le
      exact weight_le_tot hnonneg c
    have hfit := (circlet_state u s t hu hs ht X hcommon i).2
    have hfit' : (X.aspect true).fitsink z ∧ (X.aspect false).fitsink w :=
      not_not.mp (fun h=>hpos.ne' (hfit (z,w) h))
    have hzone : C.zone S (X,z,w) := by
      refine ⟨⟨⟨by simp,by simp,hcommon,hfit'.1,hfit'.2,
        (hgap X hcommon i (z,w)).resolve_left hpos.ne'⟩,?_⟩,?_⟩
      · intro side
        cases side
        · exact hfully
        exact hfullx
      intro side
      cases side
      · exact hy
      exact hx
    have hzero:=hf' _ (C.band_write S hzone)
    rw [hab] at hzero
    change a.read x.q z.2+b.read x.q w.2=0 at hzero
    change a.read x.q z.2=b.read y.q w.2
    rw [←hq]
    exact add_right_cancel (hzero.trans (char_two _).symm)
  obtain ⟨φ,hφ,hφ'⟩:=generic_status_predictors hs.law ht.law i (S true) (S false)
    ((hS true).trans_lt hB) ((hS false).trans_lt hB) hg a b hrel
  have hφall:=hleft i.1 (S true) (hS true) a φ hφ
  have hφall':=hright i.2 (S false) (hS false) b φ hφ'
  have hp : 0<circlet u s t v.1 i v.2:=hη.trans_le hv.1.2.2.2.2.2
  obtain ⟨c,hc,hcA,hcB⟩:=circlet_positive_cell hu hs ht v.1 hv.1.2.2.1 i v.2 hp
  have ha:=hφall (v.1.aspect true) (by simp) (hv.1.2.2.1 true) c hc v.2.1 hcA
  have hb:=hφall' (v.1.aspect false) (by simp) (hv.1.2.2.1 false) c hc v.2.2 hcB
  rw [hab]
  change a.soot (v.1.aspect true) v.2.1+b.soot (v.1.aspect false) v.2.2=0
  rw [ha,hb]
  exact char_two _

end
end Lax793645Proofs.Simplifications
