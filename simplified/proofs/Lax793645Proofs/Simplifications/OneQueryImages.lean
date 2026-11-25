import Lax793645Proofs.Simplifications.OneFrameImages
import Lax793645Proofs.Simplifications.OneClosedPinLaws
import Lax793645Proofs.Simplifications.OneUnitCollisions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BoundedQueryTemplates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]
  {p : Shape} {n N : ℕ}

abbrev OneForum (p : Shape) (n N : ℕ) (G : Type):=G → OneFrame p n N

def oneForumLaw (m : Mixer p n) (N : ℕ) : Wgt (OneForum p n N G):=
  prodW (fun _ : G=>quadraticChannelRaw (C:=Vec (Fin p.h))
    (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')

def onePeek (g : Route I G) (A : NomQuery p n g) (x : OneForum p n N G) : Rack I N:=
  (rackEquiv g N).symm (fun i=>onePeer (A i) (x i))

def oneDependentGram (g : Route I G) (m : Mixer p n) (A : NomQuery p n g) (x : Rack I N) : Prop:=
  ∀ i,let z:=rackEquiv g N x i
      (stackMatrixEquiv N z).mulVecLin.ker=(A i).mulVecLin.ker ∧
        quadraticPairCode z=quadraticGramCode (pullM (A i) (A i) (selfM p n m.mixM))

/-- The actual independent component-frame law yields the quadratic
Gram network law, with arbitrary dependencies among nominal columns. -/
theorem one_law_peek (g : Route I G) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) (A : NomQuery p n g) :
    mapW (oneForumLaw m N) (onePeek g A)=unifOn (oneDependentGram g m A) := by
  classical
  let E:=rackEquiv g N
  let f (x : OneForum p n N G):=fun i=>onePeer (A i) (x i)
  have h : mapW (oneForumLaw m N) f=mapW (unifOn (oneDependentGram g m A)) E := by
    unfold oneForumLaw f
    rw [joint_map]
    have he : mapW (unifOn (oneDependentGram g m A)) E=
        prodW (fun i=>unifOn (fun z : Rack (Port g i) N=>
          (stackMatrixEquiv N z).mulVecLin.ker=(A i).mulVecLin.ker ∧
            quadraticPairCode z=quadraticGramCode (pullM (A i) (A i) (selfM p n m.mixM)))) := by
      exact (on_equiv E (fun y : Network g N=>∀ i,
        (stackMatrixEquiv N (y i)).mulVecLin.ker=(A i).mulVecLin.ker ∧
          quadraticPairCode (y i)=quadraticGramCode (pullM (A i) (A i) (selfM p n m.mixM)))).trans
        (uniform_pi_event (fun i (z : Rack (Port g i) N)=>
          (stackMatrixEquiv N z).mulVecLin.ker=(A i).mulVecLin.ker ∧
            quadraticPairCode z=quadraticGramCode (pullM (A i) (A i) (selfM p n m.mixM))))
    rw [he]
    apply congrArg (prodW (ι:=G))
    funext i
    exact one_peer_dependent m (A i) hN
  change mapW (oneForumLaw m N) (E.symm∘f)=_
  rw [←mapW_nested,h]
  funext x
  rw [mapW_equiv_val,mapW_equiv_val,Equiv.symm_symm,Equiv.symm_apply_apply]

def oneMerge : OneUnit p n N ≃ OneForum p n N (Ports p) where
  toFun x i:=x i.1 i.2
  invFun x i e:=x (i,e)
  left_inv _:=rfl
  right_inv _:=rfl

theorem one_law_merge (m : Mixer p n) (N : ℕ) :
    mapW (oneUnitRaw m N) oneMerge=oneForumLaw (G:=Ports p) m N := by
  classical
  funext x
  rw [mapW_equiv_val]
  simp only [oneUnitRaw,oneRaw,oneForumLaw,prodW,Fintype.prod_prod_type]
  rfl

def oneScatter (t : Tagging p I) (N : ℕ) : OneKeys t N ≃ Rack (KeySlots p t) N where
  toFun x:=(fun a i=>x i.1 i.2 (Sum.inl a),fun a i=>x i.1 i.2 (Sum.inr a))
  invFun x:=fun i e a=>Sum.elim (x.1.col ⟨i,e⟩) (x.2.col ⟨i,e⟩) a
  left_inv x:=by funext i e a; cases a <;> rfl
  right_inv x:=by apply Prod.ext <;> rfl

theorem one_peek_keys (t : Tagging p I) (v : Volley p n I) (x : OneUnit p n N) :
    onePeek (globPort p t v.obj) (nomAsk t v) (oneMerge x)=
      oneScatter t N (oneVolleyKeys v t x) := by
  apply Prod.ext
  · ext a i
    change onePrimal (x (v.obj i.1) i.2.val)
      ((nomAsk t v (v.obj i.1,i.2.val))*ᵥPi.single ⟨i,rfl⟩ 1) (Sum.inl a)=_
    rw [Matrix.mulVec_single_one]
    rfl
  · ext a i
    change onePrimal (x (v.obj i.1) i.2.val)
      ((nomAsk t v (v.obj i.1,i.2.val))*ᵥPi.single ⟨i,rfl⟩ 1) (Sum.inr a)=_
    rw [Matrix.mulVec_single_one]
    rfl

/-- Exact law of the original one-frame query keys. This is the input to
the retained-column Fourier estimate, not an independent-frame proxy. -/
theorem one_raw_keys_dependent (t : Tagging p I) (v : Volley p n I) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) :
    mapW (oneUnitRaw m N) ((oneScatter t N)∘oneVolleyKeys v t)=
      unifOn (oneDependentGram (globPort p t v.obj) m (nomAsk t v)) := by
  classical
  have hh:=one_law_peek (globPort p t v.obj) m hN (nomAsk t v)
  rw [←one_law_merge m N,mapW_nested] at hh
  refine Eq.trans ?_ hh
  congr 1
  funext x
  exact (one_peek_keys t v x).symm

end
end Lax793645Proofs.Simplifications
