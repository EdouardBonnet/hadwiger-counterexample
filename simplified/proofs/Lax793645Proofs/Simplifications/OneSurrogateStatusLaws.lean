import Lax793645Proofs.Simplifications.OneStatusCharts
import Lax793645Proofs.Simplifications.OneUnaryReference
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SurrogateStatusLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}
abbrev OneSilhouette (p : Shape) (N r : ℕ):=∀ l : Tag p.g,F→OneAtomKey l N→Fin r
namespace OneAppearance
variable (x : Appearance p)
def oneFace (o : OneOrient p n N) (w : Knobs p.g n) : OneAtomKey (p:=p) x.l N :=
  oneDesc x.trot w o
def oneProfile {d : ℕ} (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d)
    (z : Knobs p.g n) : Magazine p d :=
  oneSpecify p i v m o x.l x.s x.f z
variable (Y : OneSilhouette p N r)
def oneShowTag (o : OneOrient p n N) := fun w=>Y x.l x.q (oneFace x o w)

def oneReference := mapW (oneLawOmega p N x.l x.q) (Y x.l x.q)
def oneEmpirical (o : OneOrient p n N) := mapW (x.wit n) (oneShowTag x Y o)

variable {d : ℕ}
def oneReflected (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d) (a : Fin r) :=
  mapW (stained (x.wit n) (oneShowTag x Y (o i)) a) (oneProfile x i o m v)

theorem oneReflectedLaw (h : IsLaw (x.wit n)) (i : Nodes)
    (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d)
    (a : Fin r) : IsLaw (oneReflected x Y i o m v a) :=
  mapW_law (stained_law _ h _) _

def oneClose (o : OneOrient p n N) (ε : ℝ) :=
  varOne (oneReference x Y) (oneEmpirical x Y o) ≤ ε
end OneAppearance

namespace OneAppearance
variable (x : Appearance p) (Y : OneSilhouette p N r)
variable {d : ℕ}

theorem oneClose_expect (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d)
    (hw : IsLaw (x.wit n)) (u : Fin r → Magazine p d→ ℝ) (hu : ∀ i j, |u i j| ≤ 1)
    {ε : ℝ} (h : oneClose x Y (o i) ε) :
    |avg (oneReference x Y) (fun a=> avg (oneReflected x Y i o m v a) (u a))-
     avg (x.wit n) (fun a=>u (oneShowTag x Y (o i) a) (oneProfile x i o m v a))|≤ ε := by
  rw [inside_color _ hw]
  refine le_trans (varError (oneReference x Y) (oneEmpirical x Y (o i)) _ (fun j=>?_)) h
  let w := oneReflected x Y i o m v j
  have he : IsLaw w:= oneReflectedLaw x Y hw i o m v j
  exact (abs_avg_le he.nz).trans ((avg_mono he.nz (hu j)).trans_eq (he.avg_const _))

theorem oneShow_pr (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d)
    (hw : IsLaw (x.wit n)) (j : Fin r) (U : Magazine p d→Prop) :
    pr (x.wit n) (fun y => oneShowTag x Y (o i) y=j∧ U (oneProfile x i o m v y))=
      oneEmpirical x Y (o i) j * pr (oneReflected x Y i o m v j) U := by
  classical
  rw [pr_of_on hw.nz]
  unfold oneReflected oneEmpirical
  rw [mapW_pr]
  let f:=oneShowTag x Y (o i)
  let w:= x.wit n
  by_cases h : mapW w f j ≠0
  · unfold stained; rw [if_pos h]; rfl
  have hh : pr w (fun y=> f y=j)=0 := not_not.mp h
  change pr w _*_=pr w _ * _
  rw [hh,zero_mul,zero_mul]

theorem oneReflection_exact (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d)
    (j : Fin r) (P : Magazine p d→Prop)
    (hw : carried (x.wit n) (P ∘ oneProfile x i o m v)) :
    carried (oneReflected x Y i o m v j) P := by
  unfold oneReflected
  let f := P∘oneProfile x i o m v
  refine mapW_carried (p:=f) ?_ (fun _ hh=>hh)
  unfold stained; split
  next h =>
    refine normW_carried ?_; intro a ha
    unfold subW; rw [hw a ha,zero_mul]
  next => exact hw
end OneAppearance
end
end Lax793645Proofs.Simplifications
