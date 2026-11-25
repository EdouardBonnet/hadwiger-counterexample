import Lax793645Proofs.Simplifications.JointPredictorCoordinates
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FreeBlockFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Submodule Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def primalKey (o : Orient p n N) : Ray p n→ₗ[F]PairedKeys (Comp p.g) (Fin N) where
  toFun v:=fun e=>(primary (o e).1*ᵥv,primary (o e).2*ᵥv)
  map_add' x y:=by ext e <;> simp [Matrix.mulVec_add]
  map_smul' a x:=by
    rcases bit_cases a with h|h <;> subst a <;> ext e <;> simp

theorem star_primal_key (o : Orient p n N) (l : Tag p.g) (s : Label p.b)
    (z : Base p.g n) : starKey l (primalKey o (point p s z))=keyOne p l s z o := by
  ext e b j
  cases b <;> rfl

theorem primal_key_free (o : Orient p n N) (s : Label p.b) (z : Vec (Fin n)) :
    primalKey o (blockRay p n s Block.Z*ᵥz)=
      frameFreeKey (selectorFreeColumns p n s) o z := by
  classical
  ext e b
  all_goals
    simp only [primalKey,frameFreeKey,LinearMap.coe_mk,AddHom.coe_mk,
      selectorFreeColumns,Matrix.mulVec_mulVec,←Matrix.mul_assoc,mul_embedMat]
    rfl

def queryCell (H : Space (PairedKeys (Comp p.g) (Fin N))) (o : Orient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) (x : Knobs p.g n) :=
  jointCell H (primalKey o (spring p l s f x))

theorem query_cell_update (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) (z : Vec (Fin n)) :
    queryCell H o l s f (update x Block.Z z)=
      ((jointCell H).comp (frameFreeKey (selectorFreeColumns p n s) o)) z+
        queryCell H o l s f (update x Block.Z 0) := by
  unfold queryCell
  rw [spring_update p l s f x Block.Z (Flavor.keepZ f l),map_add,map_add,primal_key_free]
  exact add_comm _ _

/-- The conditional cell law is exactly uniform for each assignment of
the other coordinates. There is no division by a cell probability. -/
theorem joint_key_fiber_law (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (s : Label p.b)
    (h : Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
    (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :
    mapW unif (fun z : Vec (Fin n)=>queryCell H o l s f (update x Block.Z z))=unif := by
  classical
  let A:=(jointCell H).comp (frameFreeKey (selectorFreeColumns p n s) o)
  have hA : Surjective A:=joint_cell_free_surjective _ o H h
  let b:=queryCell H o l s f (update x Block.Z 0)
  let e : Module.Dual F H≃Module.Dual F H:=
    ⟨fun c=>c+b,fun c=>c-b,fun c=>add_sub_cancel_right c b,fun c=>sub_add_cancel c b⟩
  have he : (fun z : Vec (Fin n)=>queryCell H o l s f (update x Block.Z z))=
      e ∘ A := by
    funext z
    exact query_cell_update H o l s f x z
  rw [he]
  funext c
  change pr unif (fun z=>e (A z)=c)=_
  rw [←mapW_pr unif A (fun y=>e y=c),map_unif_surjective A hA]
  change mapW unif e c=unif c
  rw [unif_equiv]

/-- A law preserving free Z coordinates has a uniform common cell,
independent of every observable unchanged by refreshing Z. This includes
the tester bits and the finite clean-coordinate restrictions. -/
theorem joint_key_independence (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (s : Label p.b)
    (h : Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
    (l : Tag p.g) (f : Flavor p.g) (μ : Wgt (Knobs p.g n)) (hμ : flowZ p μ)
    {Y : Type} [Fintype Y] (T : Knobs p.g n→Y)
    (hT : ∀ x z,T (update x Block.Z z)=T x) :
    mapW μ (fun x=>(T x,queryCell H o l s f x))=pairW (mapW μ T) unif := by
  classical
  funext y
  change pr μ (fun x=>(T x,queryCell H o l s f x)=y)=_
  unfold pr
  rw [zavg p μ hμ]
  have he (x : Knobs p.g n) :
      avg unif (fun z=>ind ((T (update x Block.Z z),
        queryCell H o l s f (update x Block.Z z))=y))=
        ind (T x=y.1)*unif y.2 := by
    simp_rw [hT]
    have hh:=mapW_avg unif
      (fun z : Vec (Fin n)=>queryCell H o l s f (update x Block.Z z))
      (fun c=>ind ((T x,c)=y))
    rw [joint_key_fiber_law H o s h l f x] at hh
    rw [←hh]
    simp only [Prod.ext_iff,ind_and,avg_mul']
    rw [show avg unif (fun c=>ind (c=y.2))=unif y.2 from pr_point' unif y.2]
  simp_rw [he,avg_mul]
  rfl

end
end Lax793645Proofs.Simplifications
