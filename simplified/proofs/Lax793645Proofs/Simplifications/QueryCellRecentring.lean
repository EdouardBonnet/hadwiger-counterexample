import Lax793645Proofs.Simplifications.JointKeyFiberLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.NominalPointArrays

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

section General
variable {V C : Type} [AddCommGroup V] [Module F V] [AddCommGroup C] [Module F C]
  [Fintype V] [Fintype C]

theorem affine_uniform (A : V→ₗ[F] C) (hA : Surjective A) (b : C) :
    mapW unif (fun v=>A v+b)=unif := by
  let e : C≃C:=⟨fun c=>c+b,fun c=>c-b,fun c=>add_sub_cancel_right c b,
    fun c=>sub_add_cancel c b⟩
  funext c
  change pr unif (fun v=>e (A v)=c)=_
  rw [←mapW_pr unif A (fun y=>e y=c),map_unif_surjective A hA]
  change mapW unif e c=unif c
  rw [unif_equiv]

def affineRecenter (A : V→ₗ[F] C) (k : C) (s : C→ₗ[F] V) (x : V) (c : C) : V :=
  x+s (c-(A x+k))

/-- Randomizing the target cell preserves the uniform input law. The
argument uses an affine surjection, so no cell-mass denominator occurs. -/
theorem affine_recenter_uniform (A : V→ₗ[F] C) (k : C) (s : C→ₗ[F] V) :
    mapW (pairW unif unif) (fun x : V×C=>affineRecenter A k s x.1 x.2)=unif := by
  let B : V×C→ₗ[F]V:=(LinearMap.fst F V C)+
    s.comp ((LinearMap.snd F V C)-A.comp (LinearMap.fst F V C))
  have hB : Surjective B := fun v=>⟨(v,A v),by simp [B]⟩
  have he : (fun x : V×C=>affineRecenter A k s x.1 x.2)=fun x=>B x+(-s k) := by
    funext x
    simp only [affineRecenter,B,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.fst_apply,LinearMap.snd_apply,LinearMap.sub_apply,map_sub,map_add]
    abel
  rw [←pair_unif,he]
  exact affine_uniform B hB (-s k)

omit [Fintype V] [Fintype C] in
theorem affine_recenter_combination {I : Type} [Fintype I]
    (A : V→ₗ[F] C) (k : C) (s : C→ₗ[F] V) (x : I→V)
    (u : Vec I) (hu : ∑ i,u i=(1:F)) (c : C) :
    (∑ i,u i • affineRecenter A k s (x i) c)=
      affineRecenter A k s (∑ i,u i • x i) c := by
  simp only [affineRecenter,smul_add,Finset.sum_add_distrib,map_sub,map_add,
    smul_sub,Finset.sum_sub_distrib,←map_smul,←map_sum,←Finset.sum_smul,hu,one_smul]

end General

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def springLinear (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Knobs p.g n→ₗ[F]Ray p n where
  toFun x:=spring p l s f x-spring p l s f 0
  map_add' x y:=by
    funext i
    rcases i with ⟨i,_|j⟩
    · simp [spring,point_eval,baseV]
    simp only [Pi.sub_apply,Pi.add_apply,spring,point_eval,baseV]
    simp only [Option.elim'_some]
    unfold lit
    split_ifs <;> simp [mul_add]
  map_smul' a x:=by
    rcases bit_cases a with h|h <;> subst a <;> simp

def queryCellLinear (H : Space (PairedKeys (Comp p.g) (Fin N))) (o : Orient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Knobs p.g n→ₗ[F]Module.Dual F H:=
  (jointCell H).comp ((primalKey o).comp (springLinear p l s f))

theorem query_cell_affine (H : Space (PairedKeys (Comp p.g) (Fin N))) (o : Orient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) (x : Knobs p.g n) :
    queryCell H o l s f x=queryCellLinear H o l s f x+queryCell H o l s f 0 := by
  simp only [queryCellLinear,LinearMap.comp_apply,springLinear,LinearMap.coe_mk,
    AddHom.coe_mk,map_sub,sub_add_cancel,queryCell]

def freeKnob (p : Shape) (n : ℕ) : Vec (Fin n)→ₗ[F]Knobs p.g n:=
  LinearMap.single F (fun _ : Block p.g=>Vec (Fin n)) Block.Z

theorem spring_add_free (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) (z : Vec (Fin n)) :
    spring p l s f (x+freeKnob p n z)=spring p l s f x+blockRay p n s Block.Z*ᵥz := by
  classical
  have he : x+freeKnob p n z=update x Block.Z (x Block.Z+z) := by
    funext B
    by_cases hB : B=Block.Z <;> simp [freeKnob,hB]
  rw [he,spring_update p l s f x Block.Z (Flavor.keepZ f l),Matrix.mulVec_add]
  have hh:=spring_update p l s f x Block.Z (Flavor.keepZ f l) (x Block.Z)
  rw [update_eq_self] at hh
  rw [hh,add_assoc]

theorem query_cell_add_free (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) (z : Vec (Fin n)) :
    queryCell H o l s f (x+freeKnob p n z)=queryCell H o l s f x+
      ((jointCell H).comp (frameFreeKey (selectorFreeColumns p n s) o)) z := by
  unfold queryCell
  rw [spring_add_free,map_add,map_add,primal_key_free]
  rfl

theorem punch_add_free (x : Knobs p.g n) (z : Vec (Fin n)) :
    punchField p (x+freeKnob p n z)=punchField p x := by
  classical
  funext i
  have hh : asBlock i.1.1≠Block.Z := by
    rcases i with ⟨⟨⟨i,j⟩|⟨⟩,b⟩,c⟩ <;> simp [asBlock,Block.O,Block.S,Block.Z]
  unfold punchField
  simp only [Pi.add_apply,freeKnob,LinearMap.single_apply,Pi.single_eq_of_ne hh,add_zero]

def recenterQuery (H : Space (PairedKeys (Comp p.g) (Fin N))) (o : Orient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : Knobs p.g n) (c : Module.Dual F H) :=
  x+freeKnob p n (S (c-queryCell H o l s f x))

theorem recenter_query_eq (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : Knobs p.g n) (c : Module.Dual F H) :
    recenterQuery H o l s f S x c=
      affineRecenter (queryCellLinear H o l s f) (queryCell H o l s f 0)
        ((freeKnob p n).comp S) x c := by
  unfold recenterQuery affineRecenter
  rw [query_cell_affine H o l s f x]
  rfl

theorem recenter_query_compound (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : I→Knobs p.g n)
    (u : Vec I) (hu : weightsAff u) (c : Module.Dual F H) :
    compound p (fun i=>recenterQuery H o l s f S (x i) c) u=
      recenterQuery H o l s f S (compound p x u) c := by
  simp_rw [recenter_query_eq]
  exact affine_recenter_combination _ _ _ x u hu c

theorem recenter_query_cell (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n))
    (hS : ∀ c,((jointCell H).comp (frameFreeKey (selectorFreeColumns p n s) o)) (S c)=c)
    (x : Knobs p.g n) (c : Module.Dual F H) :
    queryCell H o l s f (recenterQuery H o l s f S x c)=c := by
  rw [recenterQuery,query_cell_add_free,hS,add_sub_cancel]

theorem recenter_query_punches (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : Knobs p.g n) (c : Module.Dual F H) :
    punchField p (recenterQuery H o l s f S x c)=punchField p x := punch_add_free _ _

theorem recenter_query_uniform (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (S : Module.Dual F H→ₗ[F]Vec (Fin n)) :
    mapW (pairW unif unif) (fun x : Knobs p.g n×Module.Dual F H=>
      recenterQuery H o l s f S x.1 x.2)=spins p n := by
  simp_rw [recenter_query_eq]
  rw [affine_recenter_uniform,spins,←draws_unif]

end
end Lax793645Proofs.Simplifications
