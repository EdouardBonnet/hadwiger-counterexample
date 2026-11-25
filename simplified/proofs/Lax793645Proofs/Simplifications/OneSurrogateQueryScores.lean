import Lax793645Proofs.Simplifications.OneSurrogateStatusLaws
import Lax793645Proofs.Simplifications.OneScriptGramCorrespondence
import Lax793645Proofs.Simplifications.OneSuccessfulQueries
import Lax793645Proofs.Simplifications.OneReferenceProducts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N)

def oneStencil (s : Charts p n d) (m : Mixer p n) (i : Messenger q) (v : Knobs p.g n):=
  ind (OneAppearance.oneProfile (w.allure t z i) (parcel b i) o m (s (parcel b i)) v=w.amp i)
theorem one_stencil_floor (s : Charts p n d) (m : Mixer p n) (i : Messenger q) (v) :
    |oneStencil w t z o s m i v|≤1 := by
  rw [oneStencil,abs_of_nonneg (ind_nonneg _)]
  exact ind_le_one _

variable (m : Mixer p n)
def oneSeraph (s : Charts p n d) (Y : OneSilhouette p N r) (i : Messenger q) :
    Wgt (OneAtomKey (p:=p) (t i) N):=fun h=>
  OneAppearance.oneReflected (w.allure t z i) Y (parcel b i) o m
    (s (parcel b i)) (Y (t i) (z i) h) (w.amp i)
def oneMirror (s : Charts p n d) (Y : OneSilhouette p N r) : Wgt (OneKeys t N):=fun x=>
  oneKappa (w.pen t)*prodW (oneSeraph w t z o m s Y) x

theorem one_seraph_floor (s : Charts p n d) (Y : OneSilhouette p N r)
    (i : Messenger q) (hw : IsLaw (w.policies t z n i)) (x : OneAtomKey (p:=p) (t i) N) :
    0≤oneSeraph w t z o m s Y i x ∧oneSeraph w t z o m s Y i x≤1 := by
  have h:=OneAppearance.oneReflectedLaw (w.allure t z i) Y hw (parcel b i) o m
    (s (parcel b i)) (Y (t i) (z i) x)
  exact ⟨h.nz _,(weight_le_tot h.nz _).trans h.total.le⟩

theorem one_kappa_top : oneKappa (w.pen t)≤1 := by
  have h : IsLaw (prism (oneAbbey (w.pen t))):=prodW_law (fun _=>unif_law)
  exact (weight_le_tot h.nz _).trans h.total.le

theorem one_mirror_floor (s : Charts p n d) (Y : OneSilhouette p N r)
    (hw : ∀ i,IsLaw (w.policies t z n i)) (x : OneKeys t N) :
    0≤oneMirror w t z o m s Y x ∧oneMirror w t z o m s Y x≤1 := by
  have h₀ : 0≤prodW (oneSeraph w t z o m s Y) x:=
    prodW_nonneg (fun i y=>(one_seraph_floor w t z o m s Y i (hw i) y).1) x
  have h₁ : prodW (oneSeraph w t z o m s Y) x≤1 :=
    (Finset.prod_le_prod (s:=univ) (g:=fun _ : Messenger q=>(1:ℝ))
      (fun i _=>(one_seraph_floor w t z o m s Y i (hw i) (x i)).1)
      (fun i _=>(one_seraph_floor w t z o m s Y i (hw i) (x i)).2)).trans_eq (by simp)
  exact ⟨mul_nonneg (one_kappa_pos (w.pen t)).le h₀,
    (mul_le_mul (one_kappa_top w t) h₁ h₀ zero_le_one).trans_eq (one_mul _)⟩

def oneSheen (s : Charts p n d) (Y : OneSilhouette p N r) (W : Wgt (OneKeys t N)):=
  avg (oneLawNu p N t z) (fun x=>oneMirror w t z o m s Y x*W x)

theorem one_painted (s : Charts p n d) (x : Inputs p n (Messenger q)) :
    prodW (oneStencil w t z o s m) x=ind (onePrinted b s t w.sel w.flav m o x=w.amp) := by
  rw [funext_iff,ind_all]
  rfl

def oneProwl (s : Charts p n d) (W : Wgt (OneKeys t N)):=
  avg ((w.pen t).state z n) (fun x=>W (oneVolleyKeys ((w.pen t).draw x) t o)*
    ind (onePrinted b s t w.sel w.flav m o x=w.amp ∧
      ((w.pen t).draw x).reads (reducedScript w.script) m ∧oneOwnKeyPart t z (oneVolleyKeys ((w.pen t).draw x) t o)))

theorem one_sheen_sun (s : Charts p n d) (Y : OneSilhouette p N r) (W : Wgt (OneKeys t N)) :
    oneSheen w t z o m s Y W=oneKappa (w.pen t)*
      avg (oneLawNu p N t z) (fun x=>W x*prodW (oneSeraph w t z o m s Y) x) := by
  unfold oneSheen oneMirror
  rw [←avg_mul']
  apply avg_congr
  intro x _
  ring

theorem one_sales_prowl (s : Charts p n d) (π : Wgt (OneUnit p n N))
    (P : OneUnit p n N→Prop) (W : Wgt (OneKeys t N)) :
    avg (oneSales w t z π P m s) (W∘oneQueryCoordinateEquiv t N)=
      avg π (fun o=>ind (P o)*oneProwl w t z o m s W) := by
  rw [one_sales_mean]
  apply avg_congr
  intro o _
  unfold oneProwl
  rw [←avg_mul']
  apply avg_congr
  intro x _
  have he : oneQueryCoordinateEquiv t N (oneTemplateCoordinates (w.pen t) o x)=
      oneVolleyKeys ((w.pen t).draw x) t o := by
    apply (oneQueryCoordinateEquiv t N).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  simp only [Function.comp_apply,he,ind_and]
  have hkey : oneOwnPart t z (oneTemplateCoordinates (w.pen t) o x)=
      oneOwnKeyPart t z (oneVolleyKeys ((w.pen t).draw x) t o):=rfl
  rw [hkey]
  ring

end OneQuill
end
end Lax793645Proofs.Simplifications
