import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.LargeSetHits
import Lax793645Proofs.Simplifications.PredictedOverlap

/-! The actual query with its last, predicted bit left unchecked. Summing over
all choices of that bit recovers this query exactly, without normalization. -/
namespace Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis.Quill
variable {p : Shape} {q : Format} {d : Rates} {b : Bool}
  {n N K r : ℕ}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

def withInk (e : Messenger q → F) : Quill p q d b :=
  { w with amp := fun i => ((w.amp i).1, (w.amp i).2.1, e i) }

theorem withInk_moral (e : Messenger q → F) (h : w.moral t z) :
    (w.withInk e).moral t z := h

def baseDeposit (m : Mixer p n) (o : UnitType p n N) (s : Charts p n d)
    (x : Inputs p n (Messenger q)) : Prop :=
  (∀ i, w.sameInk i (printed b s t w.sel w.flav m o x i)) ∧
    ((w.pen t).draw x).reads w.script m ∧ ownPart t z ((w.pen t).resultKey o x)

def baseProwl (s : Charts p n d) (m : Mixer p n) (o : UnitType p n N)
    (W : Wgt (Keys (p:=p) t N)) : ℝ :=
  avg ((w.pen t).state z n) (fun x => ind (w.baseDeposit t z m o s x) *
    W ((w.pen t).resultKey o x))

def baseSeraph (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (i : Messenger q) : Wgt (AtomKey (p:=p) (t i) N) :=
  fun k => pr ((w.allure t z i).reflected Y (parcel b i) o m (s (parcel b i))
    (Y (t i) (z i) k)) (w.sameInk i)

def baseMirror (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (x : Keys (p:=p) t N) : ℝ :=
  (w.pen t).kappa * prodW (w.baseSeraph t z o m s Y) x

def baseSheen (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (W : Wgt (Keys (p:=p) t N)) : ℝ :=
  avg (lawNu p N t z) (fun x => w.baseMirror t z o m s Y x * W x)

theorem baseDeposit_ink (m : Mixer p n) (o : UnitType p n N) (s : Charts p n d)
    (x : Inputs p n (Messenger q)) :
    ind (w.baseDeposit t z m o s x) =
      ∑ e : Messenger q → F, ind ((w.withInk e).deposit t z m o s x) := by
  classical
  let e : Messenger q → F := fun i => (printed b s t w.sel w.flav m o x i).2.2
  have he : w.baseDeposit t z m o s x ↔ (w.withInk e).deposit t z m o s x := by
    constructor
    · rintro ⟨ha, hb, hc⟩
      refine ⟨funext fun i => Prod.ext (ha i).1 (Prod.ext (ha i).2 rfl), hb, hc⟩
    · rintro ⟨ha, hb, hc⟩
      refine ⟨fun i => ?_, hb, hc⟩
      have hi := congr_fun ha i
      change printed b s t w.sel w.flav m o x i =
        ((w.amp i).1, (w.amp i).2.1, e i) at hi
      have h1 := congrArg (fun a : Magazine p (d (parcel b i)) => a.1) hi
      have h2 := congrArg (fun a : Magazine p (d (parcel b i)) => a.2.1) hi
      exact ⟨h1,h2⟩
  rw [Finset.sum_eq_single e, he]
  · intro f _ hf
    apply ind_zero
    intro h
    apply hf
    funext i
    exact (congrArg (fun a => a.2.2) (congr_fun h.1 i)).symm
  · simp

theorem baseProwl_ink (s : Charts p n d) (m : Mixer p n) (o : UnitType p n N)
    (W : Wgt (Keys (p:=p) t N)) :
    w.baseProwl t z s m o W = ∑ e : Messenger q → F, (w.withInk e).prowl s t z m o W := by
  classical
  unfold baseProwl
  simp_rw [baseDeposit_ink, Finset.sum_mul, avg_sum]
  rfl

theorem sameInk_sum (i : Messenger q) (μ : Wgt (Magazine p (d (parcel b i)))) :
    pr μ (w.sameInk i) = ∑ e : F, μ ((w.amp i).1, (w.amp i).2.1, e) := by
  classical
  unfold pr avg
  simp only [Fintype.sum_prod_type]
  simp [sameInk, Appearance.nearly, Prod.ext_iff, ind, mul_ite, ite_and]

theorem baseSeraph_ink (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (i : Messenger q) (k : AtomKey (p:=p) (t i) N) :
    w.baseSeraph t z o m s Y i k = ∑ e : F,
      ((w.allure t z i).reflected Y (parcel b i) o m (s (parcel b i))
        (Y (t i) (z i) k)) ((w.amp i).1, (w.amp i).2.1, e) :=
  w.sameInk_sum i _

theorem baseMirror_ink (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (x : Keys (p:=p) t N) :
    w.baseMirror t z o m s Y x =
      ∑ e : Messenger q → F, (w.withInk e).mirror t z o m s Y x := by
  classical
  unfold baseMirror prodW
  simp_rw [baseSeraph_ink]
  rw [Fintype.prod_sum, Finset.mul_sum]
  rfl

theorem baseSheen_ink (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (W : Wgt (Keys (p:=p) t N)) :
    w.baseSheen t z o m s Y W =
      ∑ e : Messenger q → F, (w.withInk e).sheen t z o m s Y W := by
  classical
  unfold baseSheen
  simp_rw [baseMirror_ink, Finset.sum_mul, avg_sum]
  rfl

structure baseSteady (m : Mixer p n) (K : ℕ) (s : Charts p n d)
    (o : UnitType p n N) : Prop where
  frame : PreparationParameters.frameSide p m o
  steadyAxes (i : Messenger q) : prelim (b:=b) K s i
  enough (i : Messenger q) : (w.amp i).1.diagO = (w.amp i).2.1.1

theorem baseSeraph_floor (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (i : Messenger q)
    (hw : IsLaw (w.policies t z n i)) (k) :
    0 ≤ w.baseSeraph t z o m s Y i k ∧ w.baseSeraph t z o m s Y i k ≤ 1 := by
  have h := (w.allure t z i).reflectedLaw Y hw (parcel b i) o m (s (parcel b i))
    (Y (t i) (z i) k)
  exact ⟨pr_nonneg h.nz, (pr_le_tot h.nz).trans h.total.le⟩

theorem baseMirror_floor (o : UnitType p n N) (m : Mixer p n) (s : Charts p n d)
    (Y : Silhouette p N r) (hw : ∀ i, IsLaw (w.policies t z n i))
    (x : Keys (p:=p) t N) :
    0 ≤ w.baseMirror t z o m s Y x ∧ w.baseMirror t z o m s Y x ≤ 1 := by
  have h0 : 0 ≤ prodW (w.baseSeraph t z o m s Y) x :=
    prodW_nonneg (fun i y => (w.baseSeraph_floor t z o m s Y i (hw i) y).1) x
  have h1 : prodW (w.baseSeraph t z o m s Y) x ≤ 1 := by
    have h := Finset.prod_le_prod (s:=Finset.univ) (g:=fun _ : Messenger q => (1:ℝ))
      (fun i _ => (w.baseSeraph_floor t z o m s Y i (hw i) (x i)).1)
      (fun i _ => (w.baseSeraph_floor t z o m s Y i (hw i) (x i)).2)
    simpa [prodW] using h
  exact ⟨mul_nonneg (kappa_pos _).le h0,
    (mul_le_mul (w.kappaTop t) h1 h0 zero_le_one).trans_eq (one_mul _)⟩

theorem baseThinGlaze (m : Mixer p n) (Y : Silhouette p N r) (o : UnitType p n N)
    (i : Messenger q) (s : Charts p n d) (k : AtomKey (p:=p) (t i) N)
    {δ : ℝ} (hd : 0 < δ) (hw : w.moral t z) (hp : w.baseSteady m K s o)
    (he : gauze p δ δ Y m K o) (ht : 1 ≤ p.r) (hn : 2*p.r ≤ n) :
    δ ≤ (w.allure t z i).reference Y (Y (t i) (z i) k) →
      basebeta p K/2 ≤ w.baseSeraph t z o m s Y i k := by
  intro h
  obtain ⟨h1,h2,h3⟩ := hp.steadyAxes i
  have hh := (w.allure t z i).demonstrates Y o (m:=m) (s (parcel b i)) K
    (parcel b i) (Y (t i) (z i) k) δ hd (w.amp i).1 (w.amp i).2.1.2
    (hw.2.2 i) (hw.2.1 i) ht hn h (he _) h1 h2 h3
  have h4 : ((w.amp i).1.diagO,(w.amp i).2.1.2) = (w.amp i).2.1 :=
    Prod.ext (hp.enough i) rfl
  rw [h4] at hh
  exact hh

end StatusAnalysis.Quill
end
end Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
