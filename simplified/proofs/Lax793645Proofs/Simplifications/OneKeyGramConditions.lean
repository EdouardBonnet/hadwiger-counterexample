import Lax793645Proofs.Simplifications.OneKeyReferenceLaws
import Lax793645Proofs.Simplifications.QuadraticDiagonalData
import Lax793645Proofs.Simplifications.OneBinaryForms

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def oneOwnOne (l : Tag p.g) (q : F) (x : OneAtomKey (p:=p) l N):=
  ∀ e,(hyperbolicMatrix N).toQuadraticForm' (x e)=q
def oneKeyVoice (t : Tagging p I) (x : OneKeys t N) (i j : I)
    (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)):=
  (hyperbolicMatrix N).toQuadraticForm'.polarBilin (x i ⟨e,hi⟩) (x j ⟨e,hj⟩)
def oneVerges (t : Tagging p I) (x : OneKeys t N) (i j : I):=
  ∀ e hi hj,oneKeyVoice t x i j e hi hj=0

theorem one_verges_rev (t : Tagging p I) (x : OneKeys t N) {i j : I}
    (h : oneVerges t x i j) : oneVerges t x j i := by
  intro e hi hj
  rw [oneKeyVoice,binary_polar_symm]
  exact h e hj hi

theorem one_own_key_part (t : Tagging p I) (q : I→F) (x : OneKeys t N) :
    oneOwnKeyPart t q x ↔(∀ i,oneOwnOne (t i) (q i) (x i)) ∧
      ∀ i j,i≠j→ oneVerges t x i j := by
  classical
  unfold oneOwnKeyPart oneOwnPart
  change quadraticWavePart (ownMap t q) (oneScatter t N x) ↔ _
  simp only [quadraticWavePart,quadratic_network_traced,ownMap,quadraticPairCode,quadratic_code_diagonal]
  let Q:=ownPort (p:=p) t
  let G (e : Comp p.g):=(rackEquiv Q N (oneScatter t N x) e).1ᵀ*
    (rackEquiv Q N (oneScatter t N x) e).2
  have hd i (e : Comp p.g) (hi : inc e (t i)) :
      let a : Port Q e:=⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      G e a a=(hyperbolicMatrix N).toQuadraticForm' (x i ⟨e,hi⟩) := by
    rw [hyperbolic_matrix_apply,hyperbolic_apply]
    rfl
  have he i j (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)) :
      let a : Port Q e:=⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      let b : Port Q e:=⟨⟨j,⟨e,hj⟩⟩,rfl⟩
      G e a b+G e b a=oneKeyVoice t x i j e hi hj := by
    rw [oneKeyVoice,hyperbolic_matrix_polar,hyperbolic_polar]
    rfl
  change (∀ e,(∀ a : Port Q e,G e a a=q a.val.1) ∧
    ∀ a b : Port Q e,a≠b→G e a b+G e b a=0) ↔ _
  constructor
  · intro h
    constructor
    · intro i f
      exact (hd i f.val f.property).symm.trans ((h f.val).1 _)
    · intro i j hij e hi hj
      rw [←he]
      apply (h e).2
      intro h'
      exact hij (congrArg (fun a : Port Q e=>a.val.1) h')
  · rintro ⟨h,h'⟩ e
    constructor
    · rintro ⟨⟨i,⟨a,hi⟩⟩,ha⟩
      change a=e at ha
      subst a
      exact (hd i e hi).trans (h i ⟨e,hi⟩)
    · rintro ⟨⟨i,⟨a,hi⟩⟩,ha⟩ ⟨⟨j,⟨b,hj⟩⟩,hb⟩ hab
      change a=e at ha
      change b=e at hb
      subst a
      subst b
      have hij : i≠j := by intro h; subst j; exact hab rfl
      exact (he i j e hi hj).trans (h' i j hij e hi hj)

theorem one_voice_note (v : Template p I) (x : OneUnit p n N) (z : Inputs p n I)
    (e : Comp p.g) (i j : I) (hi : inc e (v.t i)) (hj : inc e (v.t j)) :
    oneKeyVoice v.t (oneVolleyKeys (v.draw z) v.t x) i j e hi hj=
      evmat (oneDuel (x (v.aim i) e) (x (v.aim j) e)) (v.croon i (z i)) (v.croon j (z j)) := by
  rw [one_duel_value]
  rfl

theorem one_voice_same (v : Template p I) (x : OneUnit p n N) (z : Inputs p n I)
    (m : Mixer p n) (hw : ∀ i,oneFrameLaw m (x i))
    (e : Comp p.g) (i j : I) (hi : inc e (v.t i)) (hj : inc e (v.t j))
    (h : v.aim i=v.aim j) :
    oneKeyVoice v.t (oneVolleyKeys (v.draw z) v.t x) i j e hi hj=
      evmat (selfM p n m.mixM+(selfM p n m.mixM)ᵀ) (v.croon i (z i)) (v.croon j (z j)) := by
  rw [one_voice_note,h,one_duel_same m _ (hw _)]

theorem one_voices_diag (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (z : Inputs p n I) (hw : ∀ i,oneFrameLaw m (x i)) (hj : 1≤p.j) (i : I) :
    oneOwnOne (v.t i) (dialed p (v.t i) (v.f i) (z i)) (oneVolleyKeys (v.draw z) v.t x i) := by
  intro e
  let w:=(v.draw z).par i
  have hW : mom p (v.s i) w∈Wspace p n:=Submodule.subset_span ⟨_,_,rfl⟩
  have h:=one_moment_tester hj (hw (v.aim i)) e.val hW
  rw [mom,quadratic_moment_outer,mpair_outer] at h
  have he : evmat (hyperbolicMatrix N)
      (onePrimal (x (v.aim i) e.val) (v.croon i (z i)))
      (onePrimal (x (v.aim i) e.val) (v.croon i (z i)))=
        (hyperbolicMatrix N).toQuadraticForm' (oneVolleyKeys (v.draw z) v.t x i e) := by
    change evmat _ _ _=(hyperbolicMatrix N).toBilin'
      (oneVolleyKeys (v.draw z) v.t x i e) (oneVolleyKeys (v.draw z) v.t x i e)
    rw [Matrix.toBilin'_apply']
    rfl
  exact he.symm.trans (h.trans (etaScan p (n:=n) (v.t i) (v.s i) _ (z i)).symm)

end
end Lax793645Proofs.Simplifications
