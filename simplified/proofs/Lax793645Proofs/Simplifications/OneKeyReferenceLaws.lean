import Lax793645Proofs.Simplifications.OneQueryCoordinateLaws
import Lax793645Proofs.Simplifications.OneQueryHighMoment
import Lax793645Proofs.Simplifications.OneUnaryReference
import Lax793645Proofs.Simplifications.QuadraticWaveProducts
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ReferenceProductTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {p : Shape} {N : ℕ}

theorem evmat_reindex (e : I≃J) (M : Mat J J) (v : Vec J) :
    evmat (M.submatrix e e) (v∘e) (v∘e)=evmat M v v := by
  simp only [evmat,dotProduct,mulVec,submatrix_apply,Function.comp_apply]
  apply Fintype.sum_equiv e
  intro i
  congr 1
  exact e.sum_comp (fun j=>M (e i) j*v j)

theorem quadratic_code_reindex (e : I≃J) (A B : Mat J J) :
    quadraticGramCode (A.submatrix e e)=quadraticGramCode (B.submatrix e e) ↔
      quadraticGramCode A=quadraticGramCode B := by
  constructor
  · intro h
    apply Subtype.ext
    funext v
    have hh:=congrFun (congrArg Subtype.val h) (v∘e)
    change evmat (A.submatrix e e) (v∘e) (v∘e)=evmat (B.submatrix e e) (v∘e) (v∘e) at hh
    change evmat A v v=evmat B v v
    simpa only [evmat_reindex] using hh
  · intro h
    apply Subtype.ext
    funext v
    let w : Vec J:=v∘e.symm
    have hw : w∘e=v:=by funext i; simp [w]
    change evmat (A.submatrix e e) v v=evmat (B.submatrix e e) v v
    rw [←hw,evmat_reindex,evmat_reindex]
    exact congrFun (congrArg Subtype.val h) w

def oneMug (p : Shape) (l : Tag p.g) (N : ℕ) : OneAtomKey l N≃Rack (Toast p) N:=
  (oneAtomSplit l N).trans (mug p l N)
def oneTray (p : Shape) (t : Tagging p I) (N : ℕ) : OneKeys t N≃Rack (I×Toast p) N:=
  (Equiv.piCongrRight (fun i=>oneMug p (t i) N)).trans (relay I (Toast p) N).symm

def oneOwnKeyPart (t : Tagging p I) (q : I→F) (x : OneKeys t N):=
  oneOwnPart t q ((oneQueryCoordinateEquiv t N).symm x)
def oneLawNu (p : Shape) (N : ℕ) (t : Tagging p I) (q : I→F) : Wgt (OneKeys t N):=
  unifOn (oneOwnKeyPart t q)

theorem one_tray_sips (t : Tagging p I) (x : OneKeys t N) (i : I) :
    led i (oneTray p t N x)=oneMug p (t i) N (x i) := by apply Prod.ext <;> rfl

theorem one_tray_wave (t : Tagging p I) (q : I→F) (x : OneKeys t N) :
    oneOwnKeyPart t q x ↔ quadraticWavePart (trayMap p t q) (oneTray p t N x) := by
  unfold oneOwnKeyPart oneOwnPart
  change quadraticWavePart (ownMap t q) (oneScatter t N x) ↔ _
  simp only [quadraticWavePart,quadratic_network_traced]
  apply forall_congr'
  intro c
  let A:=(rackEquiv (ownPort t) N (oneScatter t N x) c).1ᵀ*
    (rackEquiv (ownPort t) N (oneScatter t N x) c).2
  change quadraticGramCode A=quadraticGramCode (ownMap t q c) ↔
    quadraticGramCode (A.submatrix (trayJoin p t c) (trayJoin p t c))=
      quadraticGramCode ((ownMap t q c).submatrix (trayJoin p t c) (trayJoin p t c))
  exact (quadratic_code_reindex (trayJoin p t c) A (ownMap t q c)).symm

theorem one_law_tray (t : Tagging p I) (q : I→F) :
    mapW (oneLawNu p N t q) (oneTray p t N)=quadraticWave (trayMap p t q) N := by
  unfold oneLawNu
  rw [show oneOwnKeyPart t q (N:=N)=(fun x=>quadraticWavePart (trayMap p t q) (oneTray p t N x))
    from funext (fun x=>propext (one_tray_wave t q x))]
  exact on_equiv ..

theorem one_law_mug (t : Tagging p I) (q : I→F) (i : I) :
    mapW (oneLawOmega p N (t i) (q i)) (oneMug p (t i) N)=
      quadraticWave (laneM (trayMap p t q) i) N := by
  have hs c : Subsingleton (Port (street (trayPort p t) i) c):=⟨fun a b=>Subtype.ext
    (channelTag_inj p (t i) (a.property.trans b.property.symm))⟩
  rw [quadratic_wave_singleton _ hs]
  rw [oneLawOmega,mapW_nested]
  have he : oneMug p (t i) N∘(oneAtomSplit (t i) N).symm=mug p (t i) N := by
    funext x
    simp [oneMug]
  rw [he]
  exact lawmug p t q i

theorem one_reference_coordinates (t : Tagging p I) (q : I→F) :
    mapW (oneLawNu p N t q) (oneQueryCoordinateEquiv t N).symm=unifOn (oneOwnPart t q) := by
  classical
  unfold oneLawNu oneOwnKeyPart
  convert on_equiv (oneQueryCoordinateEquiv t N).symm (oneOwnPart t q) using 1
  congr 1
  exact Subsingleton.elim _ _

end
end Lax793645Proofs.Simplifications
