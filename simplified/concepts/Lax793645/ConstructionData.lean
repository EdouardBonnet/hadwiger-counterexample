/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0), and the quadratic-frame construction in this submission.
The data have been collected under a public namespace for the paper's statements.
See LICENSE and NOTICE for the source history.
-/
import Mathlib

/-!
---
title: Finite spaces and maps used by the construction
type: definition
---
The construction uses binary component matrices on an odd cycle, a quadratic frame at
each component, and finite laws of queries at those frames. This module gives the
concrete types used by the individual statements. The ambient dimension in the frame
coordinates is twice the hyperbolic dimension parameter.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
abbrev F := ZMod 2

abbrev Vec (I : Type) := I → F

abbrev Mat (I J : Type) := Matrix I J F

abbrev Space (V : Type) [AddCommGroup V] [Module F V] := Submodule F V

theorem char_two {V : Type*} [AddCommGroup V] [Module F V] (x : V) : x+x=0 :=
  ZModModule.add_self x

section Linear
variable {I J K L R S : Type} [Fintype I] [Fintype J]
def evmat (M : Mat I J) (x : Vec I) (y : Vec J) := dotProduct x (M *ᵥ y)

def mpair (M : Mat I J) : Mat I J →ₗ[F] F where
  toFun A := ∑ i, ∑ j, M i j * A i j
  map_add' A B := by simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' b A := by
    simp only [Matrix.smul_apply, smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_left_comm b]

theorem mpair_comm (M A : Mat I J) : mpair M A = mpair A M := by
  dsimp [mpair]
  simp only [mul_comm]

theorem mpair_outer (M : Mat I J) (x : Vec I) (y : Vec J) :
    mpair M (vecMulVec x y) = evmat M x y := by
  dsimp [mpair,evmat,mulVec,dotProduct,vecMulVec]
  simp only [Finset.mul_sum,mul_left_comm]

/-- Apply frame maps to the two factors of every tensor. -/
def liftM (P : Mat K I) (Q : Mat L J) : Mat I J →ₗ[F] Mat K L where
  toFun A := P* A* Qᵀ
  map_add' A B := by rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' b A := by simp only [Matrix.mul_smul, Matrix.smul_mul,RingHom.id_apply]

theorem liftM_def (P : Mat K I) (Q : Mat L J) (A : Mat I J) :
    liftM P Q A = P* A* Qᵀ := rfl

theorem liftM_outer (P : Mat K I) (Q : Mat L J) (x : Vec I) (y : Vec J) :
    liftM P Q (vecMulVec x y) = vecMulVec (P *ᵥ x) (Q *ᵥ y) := by
  rw [liftM_def,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

variable [Fintype K] [Fintype L]
theorem liftM_comp (P : Mat K I) (Q : Mat L J) (P' : Mat R K) (Q' : Mat S L)
    (A : Mat I J) :
    liftM P' Q' (liftM P Q A) = liftM (P'* P) (Q'* Q) A := by
  simp only [liftM_def, Matrix.transpose_mul,Matrix.mul_assoc]

theorem mpair_liftM (P : Mat K I) (Q : Mat L J) (M : Mat K L) (A : Mat I J) :
    mpair M (liftM P Q A) = mpair (liftM Pᵀ Qᵀ M) A := by

  simp only [liftM_def, mpair, transpose_transpose, LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, transpose_apply]

  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mat_left_inv [DecidableEq I] {P : Mat K I} (hp : Function.Injective P.mulVec) :
    ∃ Q : Mat I K, Q* P = 1 := by
  classical
  have hp' : Function.Injective (P.mulVecLin) := hp
  obtain ⟨f,hf⟩ := P.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hp')
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simp only [Matrix.toLin'_one]
  change ((LinearMap.toMatrix').symm _) ∘ₗ _ = _
  rw [LinearEquiv.symm_apply_apply]
  exact hf

theorem liftM_inj {P : Mat K I} {Q : Mat L J} (hp : Function.Injective P.mulVec)
    (hq : Function.Injective Q.mulVec) : Function.Injective (liftM P Q) := by
  classical
  obtain ⟨P', hP⟩ := mat_left_inv hp
  obtain ⟨Q', hQ⟩ := mat_left_inv hq
  intro A B hab
  have hh := congrArg (liftM P' Q') hab
  rw [liftM_comp,liftM_comp,hP,hQ] at hh
  simpa only [liftM_def, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one] using hh

end Linear
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule LinearMap Function
abbrev dim (V : Type) [AddCommGroup V] [Module F V] := finrank F V

abbrev rk {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) := dim (LinearMap.range f)

variable {V W U V' : Type}
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
variable [AddCommGroup U] [Module F U] [AddCommGroup V'] [Module F V']
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function
section Generic
variable {V W U : Type}
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup U] [Module F U]
theorem rk_comp_le_right [FiniteDimensional F W] (f : V →ₗ[F] W) (g : W →ₗ[F] U) :
    rk (g ∘ₗ f) ≤ rk f := by
  dsimp only [rk]; rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

end Generic
variable {I J K : Type}
variable [Fintype I] [Fintype J]
omit [Fintype I] in
theorem rank_cast (P : Mat I J) : P.rank = rk P.mulVecLin := rfl

abbrev colSp (P : Mat I J) := range P.mulVecLin

/-- A coordinate set of basis vectors of a subspace arranged as columns. -/
def pack (S : Space (Vec I)) : Mat I (Fin (dim S)) :=
  let E : Vec (Fin (dim S)) ≃ₗ[F] S := LinearEquiv.ofFinrankEq (Vec (Fin (dim S))) S (by
    rw [finrank_pi]; simp)
  LinearMap.toMatrix' (S.subtype ∘ₗ E.toLinearMap)

theorem pack_eq {S : Space (Vec I)} :
    ∃ E : Vec (Fin (dim S)) ≃ₗ[F] S, (pack S).mulVecLin = S.subtype ∘ₗ E.toLinearMap := by
  unfold pack
  refine ⟨LinearEquiv.ofFinrankEq _ _ (by rw [finrank_pi]; simp),?_⟩
  rw [← toLin'_apply']
  exact LinearEquiv.symm_apply_apply _ _

theorem pack_inj (S : Space (Vec I)) : Function.Injective (pack S).mulVec := by
  rw [← Matrix.coe_mulVecLin]
  obtain ⟨E,he⟩ := pack_eq (S:=S)
  rw [he]
  exact Subtype.val_injective.comp E.injective

theorem colSp_pack (S : Space (Vec I)) : colSp (pack S) = S := by
  obtain ⟨E,he⟩ := pack_eq (S:=S)
  rw [colSp,he,LinearMap.range_comp]
  simp

omit [Fintype I] in
theorem toMat_map [DecidableEq J] (f : Vec J →ₗ[F] Vec I) :
    (LinearMap.toMatrix' f).mulVecLin = f := by
  rw [← toLin'_apply']; exact LinearEquiv.symm_apply_apply _ _

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
noncomputable section
variable {S T : Type} [Fintype S] [Fintype T]
/-- A base-coordinate slice of a vector in the product coordinate space. -/
def selectorSlice (i : T) : Vec (S × T) →ₗ[F] Vec S where
  toFun x a := x (a,i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames.CycleGeometry
open scoped BigOperators
noncomputable section
abbrev Tag := Fin

abbrev Comp (g : ℕ) :=
  {e : Tag g × Tag g // e.1 < e.2 ∧ (SimpleGraph.cycleGraph g).Adj e.1 e.2}

def degree (g : ℕ) := min 2 (g-1)

def edge {g : ℕ} (l d : Tag g) (h : (SimpleGraph.cycleGraph g).Adj l d) : Comp g :=
  if hl : l < d then ⟨(l,d),hl,h⟩ else
    ⟨(d,l),lt_of_le_of_ne (le_of_not_gt hl) h.ne.symm,h.symm⟩

theorem edge_eq {g : ℕ} {l d : Tag g} (h : l < d)
    (ha : (SimpleGraph.cycleGraph g).Adj l d) : edge l d ha=⟨(l,d),h,ha⟩ := by
  simp [edge,h]

theorem edge_symm {g : ℕ} {l d : Tag g} (h : (SimpleGraph.cycleGraph g).Adj l d) :
    edge l d h=edge d l h.symm := by
  rcases lt_or_gt_of_ne h.ne with e|e
  · simp [edge,e,not_lt.mpr e.le]
  · simp [edge,e,not_lt.mpr e.le]

def inc {g : ℕ} (e : Comp g) (l : Tag g) := e.val.1=l ∨ e.val.2=l

theorem inc_edge_iff {g : ℕ} {l d x : Tag g} (h : (SimpleGraph.cycleGraph g).Adj l d) :
    inc (edge l d h) x ↔ l=x ∨ d=x := by
  by_cases e : l< d <;> simp [inc,edge,e,or_comm]

def next {g : ℕ} (l : Tag g) : Tag g :=
  ⟨(l.val+1)%g,Nat.mod_lt _ (by have := l.isLt; omega)⟩

theorem next_eq_add {g : ℕ} [NeZero g] (l : Tag g) : next l=l+1 := by
  apply Fin.ext
  simp [next,Fin.val_add,Nat.add_mod_mod]

theorem adjacent_next {g : ℕ} (hg : 2≤ g) (l : Tag g) :
    (SimpleGraph.cycleGraph g).Adj l (next l) := by
  rcases g with _|_|k
  · omega
  · omega
  rw [next_eq_add,SimpleGraph.cycleGraph_adj]
  exact Or.inr (add_sub_cancel_left l 1)

def forward {g : ℕ} (hg : 2≤ g) (l : Tag g) : Comp g := edge l (next l) (adjacent_next hg l)

theorem inc_forward {g : ℕ} (hg : 2≤ g) (l t : Tag g) :
    inc (forward hg l) t ↔ l=t ∨ next l=t := inc_edge_iff _

theorem forward_injective {g : ℕ} (hg : 3≤ g) : Function.Injective (forward (by omega : 2≤ g)) := by
  have : NeZero g := ⟨by omega⟩
  intro l d he
  have h1 : inc (forward (by omega : 2≤ g) d) l := by
    rw [←he]; exact (inc_forward _ _ _).mpr (Or.inl rfl)
  have h2 : inc (forward (by omega : 2≤ g) d) (next l) := by
    rw [←he]; exact (inc_forward _ _ _).mpr (Or.inr rfl)
  rcases (inc_forward _ _ _).mp h1 with h|h
  · exact h.symm
  rcases (inc_forward _ _ _).mp h2 with h'|h'
  · simp only [next_eq_add] at h h'
    have hx : d+1+1=d := by rw [h,←h']
    have hx' : d+(1+1)=d+0 := by simpa only [add_assoc,add_zero] using hx
    have hz := congrArg Fin.val (add_left_cancel hx')
    change (1%g+1%g)%g=0 at hz
    rw [Nat.mod_eq_of_lt (by omega : 1< g),Nat.mod_eq_of_lt (by omega : 1+1< g)] at hz
    omega
  simp only [next_eq_add] at h'
  exact add_right_cancel h'.symm

theorem forward_surjective {g : ℕ} (hg : 2≤ g) : Function.Surjective (forward hg) := by
  rcases g with _|_|k
  · omega
  · omega
  rintro ⟨⟨l,d⟩,hlt,ha⟩
  rcases SimpleGraph.cycleGraph_adj.mp ha with h|h
  · have hd : next d=l := by rw [next_eq_add]; simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm
    refine ⟨d,?_⟩
    unfold forward
    simp only [hd]
    rw [edge_symm,edge_eq hlt]
  · have hl : next l=d := by rw [next_eq_add]; simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm
    refine ⟨l,?_⟩
    unfold forward
    simp only [hl]
    rw [edge_eq hlt]

def forwardEquiv {g : ℕ} (hg : 3≤ g) : Tag g ≃ Comp g :=
  Equiv.ofBijective (forward (by omega : 2≤ g))
    ⟨forward_injective hg,forward_surjective (by omega)⟩

/-- A total outgoing projection, including the empty one-tag geometry. -/
def outgoingMap {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (l : Tag g) : (Comp g → V) →ₗ[ZMod 2] V :=
  if hg : 2≤ g then LinearMap.proj (forward hg l) else 0

/-- The starting vertex of an edge in the matching obtained by deleting t. -/
def matchingVertex {g : ℕ} (t : Tag g) (i : Fin ((g-1)/2)) : Tag g :=
  ⟨2* i.val+1,by have := i.isLt; omega⟩+t

def matchingMap {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (t : Tag g) : (Comp g → V) →ₗ[ZMod 2] V :=
  ∑ i : Fin ((g-1)/2),outgoingMap (matchingVertex t i)

end
end Lax793645.ConstructionData.Frames.CycleGeometry
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
abbrev Tag := Fin

abbrev Comp := Lax793645.ConstructionData.Frames.CycleGeometry.Comp

abbrev tagDegree := Lax793645.ConstructionData.Frames.CycleGeometry.degree

def inc {g : ℕ} (e : Comp g) (l : Tag g) := e.val.1=l ∨ e.val.2=l

instance {g : ℕ} (e : Comp g) (l : Tag g) : Decidable (inc e l) :=
  inferInstanceAs (Decidable (_ ∨ _))

abbrev TagStar {g : ℕ} (l : Tag g) := {e : Comp g // inc e l}

variable {g : ℕ}
/-- A private ordinary block belongs only to its owner.  Empty degenerate
geometries retain no ordinary block. -/
def allowed (d l : Tag g) := 1< g ∧ d=l

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
/-- Construction parameters that affect dimensions (except n,N). j = selector degree;
r = number of ordered tester pairs in a tester. J, h mix and channel indices. -/
structure Shape where
  g : ℕ
  b : ℕ
  j : ℕ
  J : ℕ
  r : ℕ
  h : ℕ

abbrev Block (g : ℕ) := (Tag g × Tag g) ⊕ Fin 3

namespace Block
variable {g : ℕ}
abbrev O (d t : Tag g) : Block g := .inl (d,t)

abbrev S : Block g := .inr 0

abbrev sharp : Block g := .inr 1

abbrev Z : Block g := .inr 2

end Block
abbrev BaseIdx (g n : ℕ) := Block g × Fin n

abbrev Base (g n : ℕ) := Vec (BaseIdx g n)

abbrev AIdx (g n : ℕ) := Option (BaseIdx g n)

abbrev Label (b : ℕ) := Vec (Fin b)

abbrev SelIdx (b j : ℕ) := { m : Finset (Fin b) // m.card ≤ j }

abbrev Row (p : Shape) (n : ℕ) := SelIdx p.b p.j × AIdx p.g n

abbrev Ray (p : Shape) (n : ℕ) := Vec (Row p n)

abbrev Moment (p : Shape) (n : ℕ) := Mat (Row p n) (Row p n)

def psize (p : Shape) := Fintype.card (SelIdx p.b p.j)

def emptySel {b j} : SelIdx b j := ⟨∅,by simp⟩

def selV {b} (j) (s : Label b) : Vec (SelIdx b j) := fun x => ∏ i ∈ x.val, s i

def baseV {g n} (z : Base g n) : Vec (AIdx g n) := Option.elim' 1 z

variable (p : Shape)
variable {n : ℕ}
/-- Embedding of the affine coordinate space at a fixed label. -/
def putLab (n : ℕ) (s : Label p.b) : Vec (AIdx p.g n) →ₗ[F] Ray p n where
  toFun z r := selV p.j s r.1 * z r.2
  map_add' z w := by ext; simp only [Pi.add_apply,mul_add]
  map_smul' b z := by ext; simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul]; ring

def point (s : Label p.b) (z : Base p.g n) : Ray p n := putLab p n s (baseV z)

def mom (s : Label p.b) (z : Base p.g n) : Moment p n := vecMulVec (point p s z) (point p s z)

/-- O-blocks disallowed at l are set to zero. -/
def allows {g n} (l : Tag g) (z : Base g n) :=
  ∀ d t : Tag g, ¬ allowed d l → ∀ i : Fin n, z (Block.O d t,i) = 0

def Wtag (n : ℕ) (l : Tag p.g) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, allows l z ∧ m = mom p s z}

variable {p}
/-- Cut profiles in the direct sum over unordered components. -/
abbrev Profile (p : Shape) (n : ℕ) := Comp p.g → Moment p n

def cut (p : Shape) (n : ℕ) : (Tag p.g → Moment p n) →ₗ[F] Profile p n where
  toFun w e := w e.val.1 + w e.val.2
  map_add' w w' := by
    funext e
    simp only [Pi.add_apply]
    ac_rfl
  map_smul' b w := by funext; simp only [Pi.smul_apply, RingHom.id_apply, smul_add]

def Xspace (p : Shape) (n : ℕ) : Space (Profile p n) :=
  (Submodule.pi Set.univ (fun l => Wtag p n l)).map (cut p n)

/-- Single star atoms as profiles in ambient coordinates. -/
def atom (p : Shape) (l : Tag p.g) (s : Label p.b) (z : Base p.g n) : Profile p n :=
  cut p n (Pi.single l (mom p s z))

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
variable {S T : Type} [Fintype S] [Fintype T]
def tensorRay (s : Vec S) (t : Vec T) : Vec (S × T) := fun x => s x.1* t x.2

def affineTensorSpace (εS : Vec S) (εT : Vec T) : Space (Mat (S × T) (S × T)) :=
  Submodule.span F {w | ∃ s t, dotProduct εS s=1 ∧ dotProduct εT t=1 ∧
    w=vecMulVec (tensorRay s t) (tensorRay s t)}

structure TensorIdentities (εS : Vec S) (εT : Vec T)
    (w : Mat (S × T) (S × T)) : Prop where
  selector_sym : ∀ a b i j, w (a,i) (b,j)=w (b,i) (a,j)
  base_sym : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i)
  selector_diag : ∀ a i j, w (a,i) (a,j)=∑ b, εS b* w (a,i) (b,j)
  base_diag : ∀ a b i, w (a,i) (b,i)=∑ j, εT j* w (a,i) (b,j)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {b : ℕ}
def monoBit (s : Label b) (S : Finset (Fin b)) := ∏ i ∈ S, s i

variable {p : Shape} {n : ℕ}
def labMat (p : Shape) (n) (s : Label p.b) :
    Mat (Row p n) (AIdx p.g n) :=
  Matrix.of (fun v i => if v.2=i then monoBit s v.1.val else 0)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
theorem mpair_add {I J : Type} [Fintype I] [Fintype J] (A B M : Mat I J) :
    mpair (A+B) M = mpair A M + mpair B M := by rw [mpair_comm,map_add,mpair_comm M,mpair_comm M]

theorem mpair_smul {I J : Type} [Fintype I] [Fintype J] (b : F) (A M : Mat I J) :
    mpair (b • A) M = b * mpair A M := by rw [mpair_comm,map_smul,mpair_comm M, smul_eq_mul]

variable (p : Shape)
def pick (n : ℕ) (u : SelIdx p.b p.j) (d : Block p.g) (i : ℕ) : Ray p n :=
  if h : i < n then Pi.single (u,some (d,⟨i,h⟩)) 1 else 0

def testM (n : ℕ) (d : Block p.g) : Moment p n :=
  ∑ i : Fin p.r, vecMulVec (pick p n emptySel d (2* i.val))
    (pick p n emptySel d (2* i.val+1))

def etab (n) (d : Block p.g) : Moment p n →ₗ[F] F := mpair (testM p n d)

/-- all O testers. -/
def etaO (n) : Moment p n →ₗ[F] F :=
  ∑ (d : Tag p.g), ∑ (t : Tag p.g), etab p n (Block.O d t)

def eta (n) : Moment p n →ₗ[F] F := etaO p n + etab p n Block.S

/-- The ordinary functional reads each owner's outgoing cycle component. -/
def roleT (n : ℕ) (t : Tag p.g) : Profile p n →ₗ[F] F :=
  ∑ l : Tag p.g, etab p n (Block.O l t) ∘ₗ
    Lax793645.ConstructionData.Frames.CycleGeometry.outgoingMap l

def role (n : ℕ) := ∑ t : Tag p.g, roleT p n t

/-- The shared functional sums the matching obtained by deleting t. -/
def sharedT (n : ℕ) (t : Tag p.g) : Profile p n →ₗ[F] F :=
  etab p n Block.S ∘ₗ Lax793645.ConstructionData.Frames.CycleGeometry.matchingMap t

def sharpPick (n : ℕ) (a : Fin p.b) (i : Fin n) : Ray p n :=
  if h : 1 ≤ p.j then pick p n ⟨{a},by simp [h]⟩ Block.sharp i.val else 0

def sharpM (n : ℕ) (Y : Fin p.b → Mat (Fin n) (Fin n)) : Moment p n :=
  ∑ a : Fin p.b, ∑ i : Fin n, ∑ j : Fin n,
    Y a i j • (vecMulVec (sharpPick p n a i) (pick p n emptySel Block.sharp j.val) +
      vecMulVec (pick p n emptySel Block.sharp i.val) (sharpPick p n a j))

def selfM (n) (Y : Fin p.b → Mat (Fin n) (Fin n)) : Moment p n :=
  ((∑ d : Tag p.g, ∑ t : Tag p.g, testM p n (Block.O d t)) +
    testM p n Block.S) + sharpM p n Y

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {U V I J K T : Type} [Fintype U] [Fintype V] [Fintype I] [Fintype J]
    [Fintype K] [Fintype T]
def embedMat [DecidableEq U] (f : I → U) : Mat U I := Matrix.of (fun i j => if i=f j then 1 else 0)

omit [Fintype U] in
theorem inj_fromCols {A : Mat U I} {B : Mat U J} (hA : Injective A.mulVec)
    (hB : Injective B.mulVec) (h : Disjoint (colSp A) (colSp B)) :
    Injective (fromCols A B).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  let a := fun i => x (Sum.inl i)
  let b := fun j => x (Sum.inr j)
  rw [fromCols_mulVec] at hx
  have he : A*ᵥa=B*ᵥb := add_right_cancel (hx.trans (char_two (B*ᵥb)).symm)
  have hi : A*ᵥa ∈ colSp A ⊓ colSp B :=
    ⟨⟨a,rfl⟩, he.symm ▸ (show B*ᵥb∈colSp B from ⟨b,rfl⟩)⟩
  rw [h.eq_bot] at hi
  have hg : A*ᵥa=0 := by simpa using hi
  have ha : a=0 := hA (hg.trans (Matrix.mulVec_zero A).symm)
  rw [he] at hg
  have hb : b=0 := hB (hg.trans (Matrix.mulVec_zero B).symm)
  funext i
  cases i
  · exact congr_fun ha _
  · exact congr_fun hb _

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}
def blockA (p : Shape) (n : ℕ) (B : Block p.g) : Mat (AIdx p.g n) (Fin n) :=
  embedMat (fun i => some (B,i))

def blockRay (p : Shape) (n : ℕ) (s : Label p.b) (B : Block p.g) : Mat (Row p n) (Fin n) :=
  labMat p n s * blockA p n B

def pullM {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I) (Q : Mat U J) :
    Mat V U →ₗ[F] Mat I J := liftM Pᵀ Qᵀ

theorem pullM_def {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I)
    (Q : Mat U J) (M : Mat V U) : pullM P Q M=Pᵀ* M* Q := rfl

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
namespace HadwigerMatching
universe u
variable {V : Type u}
/-- A finite matching whose edges are pairwise touching: each member is a
two-vertex clique, and distinct members are disjoint and joined by an edge. -/
def IsTouchingMatching (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ G.IsClique (e : Set V)) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    ∃ v ∈ e, ∃ w ∈ f, G.Adj v w)

/-- The supremum of the cardinalities of pairwise touching matchings.
For finite vertex types, this supremum is attained. -/
noncomputable def connectedMatchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), IsTouchingMatching G M ∧ M.card = n}

end HadwigerMatching
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Finset
variable {A V : Type*}
structure Holes (A : Type*) where
  rel : A → A → Prop
  sym {x y : A} : rel x y → rel y x
  irr (x : A) : ¬ rel x x
  ntri {x y z : A} : rel x y → rel y z → ¬ rel x z

namespace Holes
variable (H : Holes A)
def unit (p : A × A) := ¬H.rel p.1 p.2

def conflict (p q : A × A) := H.rel p.1 q.1 ∧ H.rel p.1 q.2 ∧ H.rel p.2 q.1 ∧ H.rel p.2 q.2

def graph (x : V → A) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ¬H.rel (x i) (x j)
  symm := ⟨fun _ _ ⟨hne,h⟩ => ⟨hne.symm,fun h' => h (H.sym h')⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Holes
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
structure Mixer (p : Shape) (n : ℕ) where
  mixL : Fin p.J → Comp p.g → Comp p.g → Moment p n
  mixR : Fin p.J → Comp p.g → Comp p.g → Moment p n
  mixM : Fin p.b → Mat (Fin n) (Fin n)

abbrev Pdual (p : Shape) (n : ℕ) := Profile p n →ₗ[F] F

def linTensor {V : Type} [AddCommGroup V] [Module F V] (a b : V →ₗ[F] F) : V →ₗ[F] V →ₗ[F] F :=
  a.smulRight b

theorem linTensor_val {V : Type} [AddCommGroup V] [Module F V] (a b : V →ₗ[F] F)
    (x y : V) : linTensor a b x y = a x * b y := rfl

variable {p : Shape} {n N : ℕ}
def T0 (p : Shape) (n : ℕ) : Profile p n →ₗ[F] Pdual p n :=
  linTensor (role p n) (role p n) +
    ∑ i : Tag p.g, (linTensor (roleT p n i) (sharedT p n i) +
      linTensor (sharedT p n i) (roleT p n i))

theorem T0_val (x y : Profile p n) : T0 p n x y =
    role p n x * role p n y +
      ∑ i : Tag p.g, (roleT p n i x * sharedT p n i y + sharedT p n i x * roleT p n i y) := by
  simp only [T0,LinearMap.add_apply,LinearMap.sum_apply,linTensor_val]

def B1 (m : Mixer p n) : Profile p n →ₗ[F] Pdual p n where
  toFun x := {
    toFun := fun y => ∑ j, ∑ e, ∑ f,
      mpair (x e) (liftM (m.mixL j e f) (m.mixR j e f) (y f))
    map_add' y z := by simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
    map_smul' b y := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_eq_mul,
      Finset.mul_sum] }
  map_add' x y := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,
      Pi.add_apply,mpair_add, Finset.sum_add_distrib]
  map_smul' b x := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,RingHom.id_apply,
      Pi.smul_apply,mpair_smul,smul_eq_mul, Finset.mul_sum]

def Tmix (m : Mixer p n) := B1 m + LinearMap.flip (B1 m)

def Tsym (m : Mixer p n) := T0 p n + Tmix m

theorem Tsym_val (m : Mixer p n) (x y : Profile p n) :
    Tsym m x y = T0 p n x y + (B1 m x y + B1 m y x) := by
  change (T0 p n + (B1 m + _)) x y = _
  simp

theorem T_swap (m : Mixer p n) (x y : Profile p n) : Tsym m x y = Tsym m y x := by
  simp only [Tsym_val,T0_val]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (mul_comm _ _)
    (Finset.sum_congr rfl fun i _ => ?_)) (add_comm _ _)
  rw [mul_comm (roleT p n i x),mul_comm (sharedT p n i x),add_comm]

def grad (m : Mixer p n) (x : Profile p n) := role p n + Tsym m x

theorem grad_val (m : Mixer p n) (x y : Profile p n) :
    grad m x y = role p n y + Tsym m x y := rfl

abbrev Ambient (p : Shape) (N : ℕ) := Comp p.g → Mat (Fin N) (Fin N)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
open scoped BigOperators
namespace HadwigerCounterexample
abbrev Wgt (α : Type*) := α → ℝ

variable {α β : Type*}
/-- Real indicator. -/
def ind (p : Prop) : ℝ := @ite ℝ p (Classical.propDecidable _) 1 0

/-- Total weight. -/
def tot [Fintype α] (w : Wgt α) : ℝ := ∑ x, w x

/-- Weighted average (not normalized if the weights are not a probability law). -/
def avg [Fintype α] (w f : Wgt α) : ℝ := ∑ x, w x * f x

/-- Weight of an event. -/
def pr [Fintype α] (w : Wgt α) (p : α → Prop) := avg w (fun x => ind (p x))

structure SubLaw [Fintype α] (w : Wgt α) : Prop where
  nz (x : α) : 0 ≤ w x
  total : tot w ≤ 1

structure IsLaw [Fintype α] (w : Wgt α) : Prop where
  nz (x : α) : 0 ≤ w x
  total : tot w = 1

/-- All positive mass is supported on `p`. We use the equivalent contrapositive with
zero mass (and supply nonnegativity wherever we speak of a law). -/
def carried (w : Wgt α) (p : α → Prop) := ∀ x : α, ¬ p x → w x = 0

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}
end Basic
/-- Restrict weights; * not* renormalized. -/
def subW (w : Wgt α) (p : α → Prop) := fun x => w x * ind (p x)

/-- Divide a finite weight function by its total, giving zero if total is zero. -/
def normW [Fintype α] (w : Wgt α) := fun x => w x / tot w

def unif [Fintype α] : Wgt α := normW fun _ => 1

def unifOn [Fintype α] (p : α → Prop) : Wgt α := normW (fun x => ind (p x))

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}
end Restrict
def pairW (w : Wgt α) (v : Wgt β) : Wgt (α × β) := fun p => w p.1 * v p.2

def mixW [Fintype α] (w : Wgt α) (F : α → Wgt β) : Wgt β := fun y => avg w (fun x => F x y)

def mapW [Fintype α] (w : Wgt α) (f : α → β) : Wgt β := fun y => pr w (fun x => f x = y)

section Prod
variable [Fintype α] [Fintype β] {w : Wgt α} {v : Wgt β}
end Prod
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
open scoped BigOperators
namespace HadwigerCounterexample
variable {ι κ α : Type*}
variable {β : ι → Type*}
def prodW [Fintype ι] (w : ∀ i, Wgt (β i)) : Wgt (∀ i, β i) := fun x => ∏ i, w i (x i)

section
variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]
end
section
variable [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ]
end
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
variable {A B : Type*} [Fintype A]
def onW (w : Wgt A) (p : A → Prop) := normW (subW w p)

variable [Fintype B]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Real
open scoped Topology
def bp (x : ℝ) := (2:ℝ)^x

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}
namespace ExpSmall
end ExpSmall
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Function LinearMap
abbrev num (I : Type) [Fintype I] : ℝ := (Fintype.card I:ℝ)

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq U] [DecidableEq I] [DecidableEq J]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B]
def semi (w : Wgt A) (k : A → Wgt B) : Wgt (A × B) := fun x => w x.1 * k x.1 x.2

variable [Fintype I] [DecidableEq I]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
instance rowDecidableEq (p : Shape) (n : ℕ) : DecidableEq (Row p n) := inferInstance

abbrev Place (p : Shape) := Comp p.g × Bool

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}
def totalRank (x : Profile p n) : ℕ := ∑ i, (x i).rank

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
def box (S : Space (Vec I)) (T : Space (Vec J)) :=
  LinearMap.range (liftM (pack S) (pack T))

theorem pack_mem_iff (v : Vec I) (S : Space (Vec I)) :
    v∈S ↔ ∃ x, pack S *ᵥ x=v := by
  change _ ↔ v∈colSp (pack S)
  rw [colSp_pack]

theorem evmat_pull (P : Mat K I) (Q : Mat L J) (A : Mat K L) (x : Vec I) (y : Vec J) :
    evmat (pullM P Q A) x y=evmat A (P *ᵥ x) (Q *ᵥ y) := by
  rw [←mpair_outer,←mpair_outer,← liftM_outer,mpair_liftM]; rfl

def annih (S : Space (Vec I)) := ker ((pack S)ᵀ.mulVecLin)

def vanish (S : Space (Vec I)) (T : Space (Vec J)) (M : Mat I J) :=
  ∀ x ∈ annih S, ∀ y∈ annih T, evmat M x y=0

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
noncomputable section
variable {S T S' T' : Type} [Fintype S] [Fintype T] [Fintype S'] [Fintype T']
def flattenMatrix : Mat S T ≃ₗ[F] Vec (S × T) where
  toFun M x := M x.1 x.2
  invFun x a i := x (a,i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tensorRectangle (U : Space (Vec S)) (V : Space (Vec T)) : Space (Vec (S × T)) :=
  (box U V).map flattenMatrix.toLinearMap

def tensorCross (U : Space (Vec S)) (V : Space (Vec T)) : Space (Vec (S × T)) :=
  tensorRectangle U ⊤ ⊔ tensorRectangle ⊤ V

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
noncomputable section
variable {S T I S' T' : Type} [Fintype S] [Fintype T] [Fintype I]
  [Fintype S'] [Fintype T']
def selectedTensorSpace (s : I → Vec S) (t : I → Vec T) : Space (Vec (S × T)) :=
  Submodule.span F (Set.range (fun i => tensorRay (s i) (t i)))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def onSide {A : Type} (x : A × A) (b : Bool) := if b then x.1 else x.2

abbrev Chan (p : Shape) := Fin p.h

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def fee (N : ℕ) (ζ : ℝ) (t : ℕ) := bp (-(1-ζ)* t* N)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {I : Type} [Fintype I]
variable {p : Shape} {n N : ℕ}
/-- One side of the lists, with actual point inputs, indexed by the
simultaneous (both units') list positions. Tags passed separately
because matched across the two sides. -/
structure Volley (p : Shape) (n : ℕ) (I : Type) where
  obj : I → Bool
  sel : I → Label p.b
  par : I → Base p.g n

abbrev Tagging (p : Shape) (I : Type) := I → Tag p.g

abbrev AtomKey {p : Shape} (l : Tag p.g) (N : ℕ) := TagStar l → Bool → Vec (Fin N)

namespace Volley
variable (v : Volley p n I)
def atomAt (t : Tagging p I) (i) := atom p (t i) (v.sel i) (v.par i)

def rayAt (i) := point p (v.sel i) (v.par i)

/-- List from endpoint j to endpoint k of the other unit. -/
def shoots (w : I → Bool) (j k : Bool) := univ.filter (fun i => v.obj i=j ∧ w i=k)

def here (j : Bool) := Finset.univ.filter (fun i => v.obj i=j)

def sumAt (t : Tagging p I) (w : I→ Bool) (j k : Bool) :=
  ∑ i∈shoots v w j k, v.atomAt t i

end Volley
namespace Volley
variable (v : Volley p n I)
end Volley
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]
namespace Volley
variable (v w : Volley p n I)
def legal (t : Tagging p I) := ∀ i : I, allows (t i) (v.par i)

def diagonalAt (i : I) := eta p n (mom p (v.sel i) (v.par i))

end Volley
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Submodule
variable {I : Type} [Fintype I]
/-- Onto projection in coordinates, killing a specified disjoint subspace. -/
structure ProjData (S T : Space (Vec I)) (A : Mat I I) : Prop where
  onto (x) : A *ᵥ x ∈ S
  fixes x : x ∈ S → A *ᵥ x=x
  kills x : x∈T → A *ᵥ x=0

theorem proj_exists (S T : Space (Vec I)) (h : Disjoint S T) :
    ∃ A, ProjData S T A := by
  classical
  obtain ⟨A,hA⟩ := mat_left_inv (inj_fromCols (pack_inj S) (pack_inj T)
    (by rw [colSp_pack, colSp_pack]; exact h))
  let B := A.toRows₁
  let C := A.toRows₂
  have he : fromRows B C * fromCols (pack S) (pack T)=1 := by
    rw [show fromRows B C=A from Matrix.fromRows_toRows A,hA]
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one] at he
  have hb : B* pack S=1 := congrArg Matrix.toBlocks₁₁ he
  have hg : B* pack T=0 := congrArg Matrix.toBlocks₁₂ he
  refine ⟨pack S* B,fun x => ?_,fun x hx => ?_,fun x hx => ?_⟩
  · rw [←mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · obtain ⟨x,rfl⟩ := (pack_mem_iff ..).mp hx
    rw [←mulVec_mulVec, mulVec_mulVec _ B, hb,one_mulVec]
  · obtain ⟨x,rfl⟩ := (pack_mem_iff ..).mp hx
    rw [←mulVec_mulVec,mulVec_mulVec _ B,hg,zero_mulVec,mulVec_zero]

variable {p : Shape} {n : ℕ}
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators
noncomputable section
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]
abbrev CallsAt (v : Volley p n I) (i : Bool) := {j : I // j ∈ v.here i}

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]
noncomputable def prj (S : Space (Vec I)) : Mat I I :=
  (proj_exists S ⊥ disjoint_bot_right).choose

variable [DecidableEq I] [DecidableEq J]
def chop (S : Space (Vec I)) := 1-prj S

abbrev Cov (p : Shape) (N : ℕ) := Place p → Space (Vec (Fin N))

def cdSign (p : Shape) {N} (S : Cov p N) (i : Bool) :=
  ∑ e : Comp p.g,dim (S (e,i))

def epoch (p : Shape) {N} (x : Ambient p N) := ∑ e : Comp p.g,(x e).rank

def erased (p : Shape) {N} (S : Cov p N) : Ambient p N →ₗ[F] Ambient p N :=
  LinearMap.pi (fun i => liftM (chop (S (i,true))) (chop (S (i,false))) ∘ₗ LinearMap.proj i)

def covered (p : Shape) {N} (S : Cov p N) (x : Ambient p N) :=
  erased p S x=0

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]
def draws (I : Type) [Fintype I] (w : Wgt A) : Wgt (I→ A) := prodW (fun _ : I => w)

variable {p : Shape} {N : ℕ}
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Finset Function
open scoped BigOperators
variable {g r n b : ℕ} {p : Shape}
abbrev Flavor (_g : ℕ) := Option Unit

namespace Flavor
abbrev full {g : ℕ} : Flavor g := none

def keeps (f : Flavor g) (x : Tag g) (y : Block g) : Prop :=
  match f,y with
  | none, .inl (i,_) => allowed i x
  | some _,.inl _ => False
  | _, .inr _ => True

instance (f : Flavor g) (x : Tag g) (y : Block g) : Decidable (keeps f x y) :=
  Classical.propDecidable _

end Flavor
abbrev Knobs (g n : ℕ) := Block g → Vec (Fin n)

def lit (f : Flavor g) (x : Tag g) (y : Knobs g n) : Base g n :=
  fun i => if f.keeps x i.1 then y i.1 i.2 else 0

def useAtom (p : Shape) {n : ℕ} (x : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) := atom p x s (lit f x y)

abbrev ProbeIdx (g : ℕ) := (Tag g × Tag g)⊕Unit

abbrev Digest (g : ℕ) := Vec (ProbeIdx g)

def asBlock (i : ProbeIdx g) : Block g := i.elim (fun q => Block.O q.1 q.2) (fun _ => Block.S)

def zget (y : Vec (Fin n)) (i : ℕ) := if h:i< n then y ⟨i,h⟩ else 0

def tested (r : ℕ) (y : Vec (Fin n)) :=
  ∑ i : Fin r,zget y (2* i.val)* zget y (2* i.val+1)

def scan (p : Shape) {n} (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :
    Digest p.g :=
  fun i => if Flavor.keeps f l (asBlock i) then tested p.r (x (asBlock i)) else 0

namespace Digest
variable (q : Digest g)
def feasible (l : Tag g) (f : Flavor g) := ∀ i,¬ Flavor.keeps f l (asBlock i) → q i=0

def diagO := ∑ d : Tag g, ∑ t,q (.inl (d,t))

def sumBit := q.diagO+q (.inr ())

end Digest
def dialed (p : Shape) {n} (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :=
  (scan p l f x).sumBit

def spins (p : Shape) (n : ℕ) : Wgt (Knobs p.g n) := draws (Block p.g) unif

/-- Projection notation for conditioning on a specified (possible)
diagnostic or diagonal only. -/
def scopedBit (p : Shape) (n : ℕ) (l : Tag p.g) (f : Flavor p.g) (q : F) :
    Wgt (Knobs p.g n) := onW (spins p n) (fun x => dialed p l f x=q)

def scopedScan (p : Shape) (n : ℕ) (l : Tag p.g) (f : Flavor p.g) (z : Digest p.g) :
    Wgt (Knobs p.g n) := onW (spins p n) (fun x => scan p l f x=z)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {A B : Type} [Fintype A] [Fintype B]
variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]
variable {p : Shape} {n N : ℕ}
abbrev HMat (p : Shape) (N : ℕ) := Mat (Fin N) (Chan p)

abbrev HFrame (p : Shape) (N : ℕ) := HMat p N × HMat p N

abbrev HCube (p : Shape) (N : ℕ) := Comp p.g → HFrame p N

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]
def nbBlock (p : Shape) := Fintype.card (Block p.g)

def ncComp (p : Shape) := Fintype.card (Comp p.g)

def dbits (p : Shape) (T R : ℕ) := ncComp p*2* psize p*(T+R)

def drow (p : Shape) (T R : ℕ) := psize p+psize p*(nbBlock p* dbits p T R)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
def wsign (x : F) : ℝ := if x = 0 then 1 else -1

variable {A B V W : Type} [Fintype A] [Fintype B]
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [Fintype V] [Fintype W]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
variable (p : Shape)
def profileA (K : ℕ) := 10*(K+1)* psize p*(p.g* p.g+5)

open Filter
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {J K : Type} [Fintype J] [Fintype K]
abbrev PhasePair (p : Shape) (N : ℕ) := HCube p N × HCube p N

abbrev Party := Vec Bool

def uPhase (p : Shape) {N} (v : HCube p N) : Ambient p N →ₗ[F] F :=
  ∑ e : Comp p.g, mpair ((v e).2*(v e).1ᵀ) ∘ₗ LinearMap.proj e

def joinPhase (p : Shape) {N} (v : PhasePair p N) (o : Party) :=
  ∑ b : Bool, o b • uPhase p (onSide v b)

variable [DecidableEq J] [DecidableEq K]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}
variable {q t : Place p→ ℕ} {S : Cov p N}
def unary (i : Bool) : Party := Pi.single i 1

variable {I J : Type} [Fintype I] [Fintype J]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}
namespace Bazaar
end Bazaar
def loseA (_ : Shape) (N x y : ℕ) := bp (-((x:ℝ)+y)* N+0.01* N)

namespace Bazaar
end Bazaar
variable {A B V : Type} [Fintype A] [Fintype B] [Fintype V]
variable [AddCommGroup V] [Module F V]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A : Type} [Fintype A]
def exponentErr (p : Shape) (m b : ℕ) (c : ℝ) :=
  let s := 2^m*(2* b)
  ((2:ℝ)^s*(2:ℝ)^s)* c^b + bp (- (p.h:ℝ)* b/2)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}
variable {A : Type} [Fintype A]
def rhUp (H c : ℝ) := (c/2)⁻¹ * H

namespace Bazaar
variable {T : Cov p N}
end Bazaar
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Function
open scoped BigOperators
variable {p : Shape} {r n : ℕ} {A I : Type} [Fintype A] [Fintype I]
variable [DecidableEq I]
def scanPrice (p : Shape) : ℝ := (1/4)^Fintype.card (ProbeIdx p.g)

def canDial (p : Shape) (l : Tag p.g) (f : Flavor p.g) (q : F) :=
  ∃ v : Digest p.g, v.feasible l f ∧ v.sumBit=q

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Function
open scoped BigOperators
variable {I J G A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {p : Shape} {n N : ℕ}
abbrev PlusRack (I : Type) (N : ℕ) := Mat (Fin N) I

abbrev Rack (I : Type) (N : ℕ) := PlusRack I N × PlusRack I N

abbrev Route (I G : Type) := I → G

abbrev Port {I G : Type} (f : Route I G) (g : G) := {i:I//f i=g}

variable [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {f : Route I G}
abbrev GeoM (f : Route I G) := ∀ i,Mat (Port f i) (Port f i)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]
def density (v w : Wgt I) := fun x => w x/v x

namespace Volley
end Volley
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
structure Template (p : Shape) (I : Type) where
  aim : I→ Bool
  t : Tagging p I
  s : I→ Label p.b
  f : I→ Flavor p.g

abbrev Inputs (p : Shape) (n : ℕ) (I : Type) := I → Knobs p.g n

namespace Template
variable (v : Template p I)
def draw (y : Inputs p n I) : Volley p n I where
  obj := v.aim
  sel := v.s
  par i := lit (v.f i) (v.t i) (y i)

def state (q : I→ F) (n : ℕ) : Wgt (Inputs p n I) :=
  prodW (fun i : I => scopedBit p n (v.t i) (v.f i) (q i))

end Template
abbrev KeySlots (p : Shape) (t : Tagging p I) := Σ i, TagStar (t i)

instance keySlotsFintype (t : Tagging p I) : Fintype (KeySlots p t) := by
  classical
  infer_instance

def ownPort (t : Tagging p I) : Route (KeySlots p t) (Comp p.g) := fun x => x.2.val

def ownMap (t : Tagging p I) (q : I→ F) : GeoM (ownPort (p:=p) t) :=
  fun _ => Matrix.diagonal (fun i => q i.val.1)

def ownOne (p : Shape) {N : ℕ} (l : Tag p.g) (q : F) (x : AtomKey (p:=p) l N) :=
  ∀ i,dotProduct (x i true) (x i false) = q

def lawOmega (p : Shape) (N : ℕ) (l : Tag p.g) (q : F) :
    Wgt (AtomKey (p:=p) l N) := unifOn (ownOne p l q)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Finset Function
variable {p : Shape} {n N : ℕ}
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K]
def layerPhase (M : Mat I J) (N : ℕ) :
    PlusRack I N →ₗ[F] (PlusRack J N →ₗ[F] F) where
  toFun X := mpair (X* M)
  map_add' X Y := LinearMap.ext fun Z => by rw [Matrix.add_mul,mpair_add,LinearMap.add_apply]
  map_smul' a X := LinearMap.ext fun Z => by rw [Matrix.smul_mul,mpair_smul,LinearMap.smul_apply]; rfl

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : ℕ}
def vectorPhase (x y : Vec I) := wsign (dotProduct x y)

abbrev Rail (I : Type) := Finset (I × I)

variable {E : Rail I}
def withinRail (M : Mat I I) (E : Rail I) :=
  ∀ i j, (i,j)∉ E→ M i j=0

def crowded (g : Route I J) : Rail I := Finset.univ.filter (fun x => g x.1=g x.2)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N : ℕ}
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
instance knFin (g n : ℕ) : Fintype (Knobs g n) := inferInstanceAs (Fintype (Knobs g n))

def freePart (p : Shape) {n} (x : Knobs p.g n) := x Block.Z

variable {g : Route I G}
namespace Template
variable (v : Template p I)
end Template
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}
abbrev MIdx (p : Shape) := Fin p.J × Comp p.g × Comp p.g

abbrev MOne (p : Shape) := (MIdx p × Bool)

def orderedM (m : Mixer p n) (i : MOne p) : Moment p n :=
  if i.2 then m.mixL i.1.1 i.1.2.1 i.1.2.2 else m.mixR i.1.1 i.1.2.1 i.1.2.2

def eitherM (b : Bool) {I : Type} (A : Mat I I) := if b then A else Aᵀ

def selfSum (m : Mixer p n) (f : Vec Bool) :=
  ∑ i : Bool,f i • eitherM i (selfM p n m.mixM)

def blockRank (d : Block p.g) (s t : Label p.b) (A : Moment p n) :=
  (pullM (blockRay p n s d) (blockRay p n t d) A).rank

/-- Matrix on a point's v coordinates for Tmix(x,atom_l). -/
def qmix (m : Mixer p n) (x : Profile p n) (l : Tag p.g) : Moment p n :=
  ∑ j : Fin p.J, ∑ f : TagStar l, ∑ e : Comp p.g,
    (liftM (m.mixL j e f.val)ᵀ (m.mixR j e f.val)ᵀ (x e) +
      liftM (m.mixL j f.val e) (m.mixR j f.val e) (x e))

def unaryGood (m : Mixer p n) (K s0 : ℕ) :=
  ∀ (x : Profile p n) (l : Tag p.g) (s : Label p.b), totalRank x ≤ K → totalRank x > 0 →
    2*(p.J-s0) ≤ blockRank Block.Z s s (qmix m x l + (qmix m x l)ᵀ)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function
open scoped BigOperators
variable {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
def prism (B : J → Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    Wgt (∀ i,Vec (B i)) := prodW (fun _ : J => unif)

def wavelength (B : J → Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :=
  prism B 0

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]
/-- list for a cross edge -/
def aiming (a b : I → Bool) (i j : Bool) :=
  Finset.univ.filter (fun x => a x=i ∧ b x=j)

/-- within-endpoint L/R bit tests. Read only a x=a y, x≠y.
(tests between ordered points; no double counting since L,R and
both orientations are in the mixer hypothesis). -/
abbrev Script (p : Shape) (I : Type) := I → I → Vec (MOne p)

namespace Volley
variable (v : Volley p n I)
def reads (s : Script p I) (m : Mixer p n) :=
  ∀ x y : I,x≠y → v.obj x=v.obj y →
    ∀ i : MOne p, s x y i = evmat (orderedM m i) (v.rayAt x) (v.rayAt y)

end Volley
def prescribedB (p : Shape) (t : Tagging p I) (s : Script p I) (x y : I) :=
  ∑ i : Fin p.J,∑ e : Comp p.g, ∑ f : Comp p.g, if inc e (t x) ∧ inc f (t y) then
    s x y ((i,e,f),true)* s x y ((i,e,f),false) else 0

noncomputable def prescribedT (p : Shape) (t : Tagging p I) (d : Vec I)
    (h : Mat I I) (s : Script p I) (x y : I) : F :=
  @ite _ (x=y) (Classical.propDecidable _) (d x)
    (h x y+(prescribedB p t s x y+prescribedB p t s y x))

def fulfills (p : Shape) (t : Tagging p I) (d f : Vec I) (u : Mat I I)
    (s : Script p I) (a b : I → Bool) :=
  ∀ (x : I) (j : Bool),
    d x+ (∑ i∈aiming a b (a x) j, prescribedT p t d u s i x) =
      if j=b x then 0 else f x

namespace Volley
variable {v : Volley p n I}
end Volley
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)
abbrev SameDuet (v : Template p I) :=
  {i : I×I//v.aim i.1=v.aim i.2 ∧ Fintype.equivFin I i.1< Fintype.equivFin I i.2}

abbrev OppDuet (v : Template p I) := {i:I×I//v.aim i.1=true∧v.aim i.2=false}

abbrev Chorus (v : Template p I) := v.SameDuet ⊕ v.OppDuet

instance : Fintype v.SameDuet := inferInstance

instance : Fintype v.OppDuet := inferInstance

/-- Self-Gram bits are tested only when the tags share a component. -/
def sharesComponent (p : Shape) (l d : Tag p.g) :=
  ∃ e : Comp p.g, inc e l ∧ inc e d

instance (p : Shape) (l d : Tag p.g) : Decidable (sharesComponent p l d) :=
  inferInstanceAs (Decidable (∃ e : Comp p.g, inc e l ∧ inc e d))

end Template
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Filter Function LinearMap
variable {p : Shape} {n N : ℕ}
namespace Template
def solo (p : Shape) (t : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Template p Unit := ⟨fun _ => true,fun _=> t,fun _ => s,fun _=> f⟩

abbrev Solo (p : Shape) := Template p Unit

variable (v : Solo p)
end Template
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
def varOne (p q : Wgt A) := ∑ x, |p x-q x|

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Filter Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
def glintRate (K : ℕ) := bp (-((K^2:ℕ):ℝ)-3)

namespace Template
variable (v : Solo p)
def stains (m : Mixer p n) (f : Vec I →ₗ[F] Profile p n) (z : Knobs p.g n) : Vec I :=
  fun i=> Tsym m (f (Pi.single i 1)) (useAtom p (v.t ()) (v.s ()) (v.f ()) z)

end Template
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)
variable {K s : ℕ}
def basebeta (p : Shape) (K : ℕ) :=
  bp (-((K^2:ℕ):ℝ)-1)* scanPrice p

end Template
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def silent (w : Pdual p n) := ∀ x, x∈Xspace p n → w x=0

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q A B T : Type} [AddCommGroup V] [Module F V]
/-- One set of linear coordinates works for every status of the prefix
(in particular, both possible diagonal bits). -/
def HasLinearCells (f : Q→ V→ A) (R : ℕ) : Prop :=
  ∃ r : ℕ,r≤ R ∧ ∃ L : V→ₗ[F] Vec (Fin r),∃ φ : Q→ Vec (Fin r)→ A,
    ∀ q x,f q x=φ q (L x)

variable {p : Shape} {N : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Finset Function Module
open scoped BigOperators
namespace StatusAnalysis
abbrev Nodes := Bool

abbrev Grid := Nodes × Nodes

abbrev Cell (d : ℕ) := Vec (Fin d)

abbrev Par (d : ℕ) := F × Cell d

abbrev Whole (d : ℕ) := Par d × F

abbrev Signal (d e : ℕ) := F × Whole d × Whole e

abbrev View (d e : ℕ) := F × Par d × Par e

abbrev Question (d e : ℕ) := F × F × Cell d × Cell e

variable {d e : ℕ}
def view (d e : ℕ) : Signal d e→ₗ[F] View d e where
  toFun x := (x.1,x.2.1.1,x.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def testV (d e : ℕ) : View d e →ₗ[F] Question d e where
  toFun x := (x.1,x.2.1.1 + x.2.2.1,x.2.1.2,x.2.2.2)
  map_add' _ _ := Prod.ext rfl (Prod.ext (add_add_add_comm ..) rfl)
  map_smul' _ _ := Prod.ext rfl (Prod.ext (mul_add _ _ _).symm rfl)

def want (d e : ℕ) := testV d e ∘ₗ view d e

def couple (d : ℕ) : Whole d→ₗ[F] F where
  toFun x := x.1.1+x.2
  map_add' _ _ := add_add_add_comm ..
  map_smul' a _ := (mul_add a _ _).symm

def coverBase (V : Space (Signal d e)) := Surjective (view d e ∘ₗ V.subtype)

abbrev Rates := Nodes→ ℕ

abbrev Suite (A B : Rates) (i : Grid) := Signal (A i.1) (B i.2)

abbrev LedgerS (A B : Rates) (i : Grid) := Question (A i.1) (B i.2)

abbrev Cabinet (A B : Rates) := ∀ i, LedgerS A B i

abbrev Quota := Vec Nodes

abbrev Court (A B : Rates) := Cabinet A B × Quota × Quota

abbrev StatusSp (A B : Rates) := ∀ i,Space (Suite A B i)

variable {A B : Rates}
def separate (A B : Rates) (i : Grid) :
    Suite A B i →ₗ[F] Court A B :=
  (LinearMap.single F (LedgerS A B) i ∘ₗ want _ _).prod
    ((LinearMap.single F (fun _ : Bool=> F) i.2 ∘ₗ
      (couple (A i.1) ∘ₗ LinearMap.fst F _ _ ∘ₗ LinearMap.snd F _ _)).prod
     (LinearMap.single F (fun _ : Bool=> F) i.1 ∘ₗ
      (couple (B i.2) ∘ₗ LinearMap.snd F _ _ ∘ₗ LinearMap.snd F _ _)))

def speak (A B : Rates) :
    (∀ i,Suite A B i) →ₗ[F] Court A B := ∑ i:Grid,separate A B i ∘ₗ LinearMap.proj i

def scorecard (V : StatusSp A B) (T : Cabinet A B) :=
  ∃ v : ∀ i,Suite A B i,(∀ i,v i∈V i) ∧ speak A B v=(T,0)

structure Critic (A B : Rates) where
  alf : ∀ i : Grid, LedgerS A B i →ₗ[F] F
  altL : Quota
  altR : Quota

def Counter (g : Critic A B) (V : StatusSp A B) :=
  ∀ i:Grid,∀ v∈V i, g.alf i (want _ _ v) =
    g.altL i.2 * couple _ v.2.1 + g.altR i.1 * couple _ v.2.2

end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {d e : ℕ}
structure DualCoefficients (A B : Rates) where
  left : Quota
  right : Quota
  gam : Grid→ F
  hed : Grid→ F
  north : (i:Grid)→ Cell (A i.1)
  south : (i:Grid)→ Cell (B i.2)

end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I] [AddCommGroup X]
    [Module F X] [AddCommGroup Y] [Module F Y]
structure Club (I X L : Type) where
  valid : I→ Prop
  writes : I→ X
  addr : I→ Bool→ L

abbrev Straps (L : Type) := Bool→ Finset L

variable (C : Club I X L)
namespace Club
def zone (s : Straps L) (i) := C.valid i ∧ ∀ b,C.addr i b∉s b

def band (s : Straps L) : Space X := Submodule.span F {x|∃ i, C.zone s i∧C.writes i=x}

def contents (p : Finset I) := ∑ i∈p,C.writes i

end Club
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
namespace StatusAnalysis
variable {I L : Type} [DecidableEq L] [DecidableEq I] {d e : ℕ}
open Club
variable {I : Grid → Type} [∀ i,DecidableEq (I i)] {A B : Rates}
abbrev Congress (I : Grid→ Type) (A B : Rates) (L : Type) := ∀ i,Club (I i) (Suite A B i) L

namespace Guild
variable (C : Congress I A B L)
end Guild
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap Submodule
open scoped BigOperators
namespace StatusAnalysis
abbrev Ax (p : Shape) (n : ℕ) (d : ℕ) := Cell d→ₗ[F] Profile p n

abbrev Charts (p : Shape) (n : ℕ) (d : Rates) := ∀ i, Ax p n (d i)

variable {p : Shape} {n N : ℕ} {d e : Rates}
abbrev Format := Grid→ ℕ

abbrev Messenger (q : Format) := Σ i:Grid,Fin (q i)

def sendId (b : Bool) (i : Grid) := if b then i.1 else i.2

def transit (b : Bool) (q : Grid) := if b then q else (q.2,q.1)

def parcel (b : Bool) {q : Format} (x : Messenger q) := sendId b x.1

def manager {q : Format} (b : Bool) (t : Tagging p (Messenger q)) (s : Messenger q→ Label p.b)
    (f : Messenger q→ Flavor p.g) : Template p (Messenger q) := ⟨parcel b,t,s,f⟩

def roll {u : ℕ} (f : Ax p n u) (g : Pdual p n) : Cell u := fun i=> g (f (Pi.single i 1))

abbrev Magazine (p : Shape) (d : ℕ) := Digest p.g × Whole d

variable {q : Format}
abbrev Amounts (p : Shape) (q : Format) (d : Rates) (b : Bool) :=
    ∀ i:Messenger q,Magazine p (d (parcel b i))

variable {H : Type} [AddCommMonoid H]
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {d e : Rates} {p : Shape} {n N : ℕ} {q : Format}
def funds {b : Bool} (x : Amounts p q d b) (i : Grid) :
    Whole (d (sendId b i)) :=
  ∑ k: Fin (q i),(x (⟨i,k⟩ : Messenger q)).2

def fullq (z : Messenger q → F) (i : Grid) := ∑ k:Fin (q i),z ⟨i,k⟩

def rhyme {b : Bool} (a : Amounts p q d b) (x : Amounts p q e (!b)) :=
  ∀ i:Grid,(funds a i).1.1+(funds x i).1.1=1

end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def owing (p : Shape) {q : Format} {d : Rates}
    (b : Bool) (a : Amounts p q d b) (u : Messenger q→ F) :=
  ∀ i,(a i).1.sumBit=u i

end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def mailRole {b} (a : Amounts p q d b) :=
  fun i=>(a i).2.1.1

def mailBias {b} (a : Amounts p q d b) :=
  fun i=>(a i).2.2

def TMill (p : Shape) {b} {d} (t : Tagging p (Messenger q)) (w : Amounts p q d b) :
    Mat (Messenger q) (Messenger q) :=
  let a (x : Tag p.g) (i : Messenger q) := ∑ z:Tag p.g,(w i).1 (Sum.inl (z,x))
  let f (x : Tag p.g) (i : Messenger q) :=
    let c:=(w i).1 (Sum.inr ())
    c+(if t i=x then c else 0)
  Matrix.of fun i j => mailRole w i * mailRole w j +
    ∑ x:Tag p.g,(a x i * f x j + f x i * a x j)

def proclaims {b : Bool} (p : Shape) {d e}
    (a : Amounts p q d b) (w : Amounts p q e (!b)) (t : Tagging p (Messenger q))
    (g : Script p (Messenger q)) :=
  fulfills p t (mailRole a) (mailBias w) (TMill p t a) g (parcel b) (parcel (!b))

end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}
def maxSpan (m b r : ℕ) := r*(2^m*(2* b))

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A : Type} [Fintype A]
abbrev Tiles (A : Type) := Finset (Finset A)

def inTiles (T : Tiles A) := fun x:A => ∃ i∈ T,x∈i

def apart (T : Tiles A) :=
  ∀ x,∀ S∈T, ∀ F∈ T,x∈S→ x∈F→ S=F

def partMass (w : Wgt A) (S : Finset A) := pr w (fun x => x∈S)

def partW (w : Wgt A) (S : Finset A) := onW w (fun x => x∈S)

def allMass (w : Wgt A) (T : Tiles A) := pr w (inTiles T)

def allW (w : Wgt A) (T : Tiles A) := onW w (inTiles T)

variable {w : Wgt A} {T : Tiles A}
def portionW (w : Wgt A) (T : Tiles A) : Wgt T :=
  fun x => partMass w x.val / allMass w T

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset
open scoped Topology
variable {A B : Type} {l : Filter A} {U : Ultrafilter A} {x y z v a : A → ℝ}
/-- At least subexponential mass. -/
def warm (l : Filter A) (z x : A→ ℝ) :=
  ∀ ε:ℝ,0<ε → ∀ᶠ i in l,bp (-ε * z i) ≤ x i

namespace warm
end warm
namespace ExpSmall
end ExpSmall
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators Topology
open Filter
variable {p : Shape} {n N : ℕ}
def mstep (r : ℕ) := 100* r+10

def Bstep (r : ℕ) := 2^(mstep r)*2

def denomStep (r : ℕ) := 10000*(r+1)^2* Bstep r

def stage (g r : ℕ) (D : ℝ) := 2* r* num (Comp g)+D+1

def pcoef (g r : ℕ) (D : ℝ) :=
  12* Bstep r+2*(denomStep r:ℝ)* stage g r D

def tinyPhase (g r : ℕ) (D : ℝ) := bp (-(pcoef g r D))

def warn := bp (-10)

def coin : ℝ := 0.0001

def heatloss (r k : ℕ) := 0.001 / (4*(r:ℝ)+k+1 : ℝ)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {A B : Type}
def named (P : A×A → Prop) (C : ℝ) :=
  ∃ k : ℕ,(k:ℝ) ≤ C ∧ ∃ S : Fin k → A → Prop,∀ y,∃ i,∀ x,P (x,y)↔S i x

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset Filter
open scoped BigOperators Topology
variable {p : Shape} {n N : ℕ}
def shine (N : ℕ) := bp (0.01* N)

def edgeError (N : ℕ) := bp (-0.005* N)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A B V : Type} [Fintype A] [Fintype B]
def allSide : Party := fun _ => 1

variable [AddCommGroup V] [Module F V] [FiniteDimensional F V]
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev Quad := Party × Party

def repeatQ (i : F) : Quad := (fun _ => i,fun _ => i)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset
open scoped BigOperators Topology
inductive PredictionClass
| dusk
| dawn (i : Bool)
| twinned
| noon
deriving Inhabited, DecidableEq

variable {p : Shape}
namespace PredictionClass
def active : PredictionClass→ Bool→ Prop
| dusk,_=> False
| dawn i,j=> i=j
| twinned,_=> True
| noon,_=> True

def firstBit (α : Party) (i : Bool) := 1+α i

def lit (c : PredictionClass) (α : Party) :=
  (∀ i,¬c.active i → firstBit α i=0) ∧
    (c=twinned → α true=α false)

end PredictionClass
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace PredictionClass
def compatible (α : Party) (x : F) : PredictionClass→ Quad→ Prop
| dusk,v=> v=repeatQ x
| dawn i,v=> v.1 i+v.2 i=firstBit α i
| twinned,v=> dotProduct allSide v.1 +dotProduct allSide v.2=0
| noon,_=> True

end PredictionClass
open PredictionClass
def glint (p : Shape) {n} (x : Bool → Profile p n) := ∑ i, role p n (x i)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
noncomputable section
variable {p : Shape} {n : ℕ}
def bitSupport {g : ℕ} (t : Fin g → F) : Finset (Fin g) :=
  Finset.univ.filter (fun l => t l≠0)

/-- Read just the ordinary testers owned by the outgoing tag. -/
def ordinaryBit (p : Shape) (n : ℕ) (x : Profile p n) (l : Tag p.g) : F :=
  ∑ t : Tag p.g,etab p n (Block.O l t) (CycleGeometry.outgoingMap l x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}
abbrev Punch (p : Shape) := ProbeIdx p.g × Fin p.r

abbrev Gauge (p : Shape) := Punch p × Bool

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass
structure PreparationParameters where
  D : ℕ
  L : ℝ
  d : ℕ
  e : ℕ
  s : ℕ
  u : ℕ
  k : ℕ
  ζ : ℝ
  B : ℕ

namespace PreparationParameters
def rank (q : PreparationParameters) := 2* q.e + 2

def leafOld (q : PreparationParameters) : ℝ := ↑q.D+q.e+2

def leafNew (q : PreparationParameters) : ℝ := q.leafOld+q.u+q.s+2

def spJoint (q : PreparationParameters) : ℝ := (q.D:ℝ)+1

def spear (q : PreparationParameters) := bp (100)* q.L

variable {p : Shape} {M n N : ℕ}
abbrev cycleM (p : Shape) := ∀ n,Mixer p n

end PreparationParameters
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary.HadwigerCounterexample
noncomputable section
variable {α : Type*} [Fintype α]
/-- Individual marginal caps (mapW denotes the actual marginals) and a joint cap. -/
def pairCaps (μ : Wgt α) (m d : ℝ) (w : Wgt (α × α)) :=
  (∀ x, mapW w Prod.fst x ≤ m * μ x) ∧
  (∀ x, mapW w Prod.snd x ≤ m * μ x) ∧
  (∀ p, w p ≤ d * pairW μ μ p)

end
end Lax793645.ConstructionData.Binary.HadwigerCounterexample
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
namespace Template
variable (v : Template p I) (z : Template p J)
instance inpFinite (p : Shape) (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) :
    Fintype (Inputs p n I) := inferInstanceAs (Fintype (I→ Knobs p.g n))

instance keySlotFinite (v : Template p I) : Fintype (KeySlots p v.t) := inferInstance

end Template
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]
variable {w : Wgt X}
def stained (w : Wgt X) (f : X→ Y) (i : Y) : Wgt X := by
  classical exact if mapW w f i≠0 then onW w (fun x => f x=i) else w

variable {μ : Wgt A}
def colored (μ : Wgt A) (w : Wgt X) (v : A→ X→ Y) :=
  semi μ (fun i => mapW w (v i))

def coloredP (w : Wgt X) (v : A→ X→ Y) (K : A→ X→ B) :=
  fun i : A×Y => mapW (stained w (v i.1) i.2) (K i.1)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]
def dip (μ f g : Wgt A) := avg μ (fun i => f i* g i)

def ode (μ f : Wgt A) := dip μ f f

def cashbook (μ : Wgt A) (f : A→ B) (g : Wgt A) :=
  fun i => mapW (fun x => μ x* g x) f i / mapW μ f i

def banner (μ : Wgt A) (f : A→ B) (g : Wgt A) := cashbook μ f g ∘ f

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ}
structure Quill (p : Shape) (q : Format) (d : Rates) (b : Bool) where
  sel : Messenger q → Label p.b
  flav : Messenger q → Flavor p.g
  amp : Amounts p q d b
  script : Script p (Messenger q)

structure Typus (p : Shape) (q : Format) (d e : Rates) where
  t : Tagging p (Messenger q)
  z : Messenger q → F
  qA : Quill p q d true
  qB : Quill p q e false

abbrev Volumes := Grid → Fin 8

abbrev Stakes (K : ℕ) := Nodes → Fin (K^2+1)

abbrev Master (K : ℕ) := Volumes × Stakes K × Stakes K

def toFormat (q : Volumes) : Format := fun i=>(q i).val

def toRates {K : ℕ} (d : Stakes K) : Rates := fun i=>(d i).val

abbrev OnFile (p : Shape) {K : ℕ} (q : Master K) :=
  Typus p (toFormat q.1) (toRates q.2.1) (toRates q.2.2)

variable {q : Format} {d e : Rates}
namespace Quill
variable {b : Bool} (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→ F)
def pen := manager b t w.sel w.flav

def moral :=
    Injective w.sel ∧ owing p b w.amp z ∧ ∀ i, (w.amp i).1.feasible (t i) (w.flav i)

end Quill
namespace Typus
variable (w : Typus p q d e)
end Typus
namespace Station
variable (w : Typus p q d e)
end Station
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {A B C H : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype H]
variable {p : Shape} {n N K M r : ℕ}
namespace StatusAnalysis
structure Appearance (p : Shape) where
  l : Tag p.g
  s : Label p.b
  f : Flavor p.g
  q : F

namespace Appearance
variable (x : Appearance p)
def apt := canDial p x.l x.f x.q

def trot := Template.solo p x.l x.s x.f

def wit (x : Appearance p) (n : ℕ) := scopedBit p n x.l x.f x.q

variable {d : ℕ}
end Appearance
namespace Appearance
variable {d : ℕ}
end Appearance
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r d : ℕ}
namespace StatusAnalysis
open Template
namespace Appearance
def nearly (p: Shape) (z: Digest p.g) (u: Par d) (x: Magazine p d) :=
  x.1=z∧ x.2.1=u

def fitsink (x : Appearance p) (w : Magazine p d) :=
   w.1.feasible x.l x.f ∧ w.1.sumBit=x.q ∧ w.1.diagO=w.2.1.1

end Appearance
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p : Shape} {n N K M r : ℕ}
namespace StatusAnalysis
variable {q:Format} {d : Rates} {b:Bool}
namespace Quill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)
def allure (i : Messenger q) : Appearance p := ⟨t i,w.sel i,w.flav i,z i⟩

variable (m : Mixer p n)
end Quill
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Module Filter Function
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
def lcost (u f g : Wgt A) := avg u (fun i=>|f i-g i|)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
def bower (f : Wgt A) := (∀ i,0≤ f i)∧ (∀ i,f i≤1)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C J : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype J]
def densityFamilyEnergy (ν : Wgt A) (μ : Wgt J) (d : J→ Wgt A) (P : A→ B) : ℝ :=
  avg μ (fun i=> ode ν (banner ν P (d i)))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {O X Y B : Type} [Fintype O] [Fintype X] [Fintype Y] [Fintype B]
def coloredCutDensities (ν : Wgt B) (κ : Wgt X) (v : O→ X→ Y) (K : O→ X→ B)
    (S : B→ Prop) : O×Y→ Wgt B :=
  fun i=> density ν (subW (coloredP κ v K i) S)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]
def linearFourier (f : Wgt (Vec I)) (ξ : Vec I) : ℝ :=
  avg unif (fun x=> vectorPhase ξ x* f x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]
def fourierNorm (f : Wgt (Vec I)) : ℝ := ∑ ξ:Vec I,|linearFourier f ξ|

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {N : ℕ}
abbrev KeyCoordinates (I : Type) (N : ℕ) := Vec (Fin N×(Bool×I))

def keyPlus : KeyCoordinates I N→ₗ[F] PlusRack I N where
  toFun x u i := x (u,(false,i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def keyMinus : KeyCoordinates I N→ₗ[F] PlusRack I N where
  toFun x u i := x (u,(true,i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def gramPrimitive (M : Mat I I) (x : KeyCoordinates I N) : F :=
  layerPhase M N (keyPlus x) (keyMinus x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J A : Type} [Fintype I] [Fintype J] [Fintype A]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] {N : ℕ}
/-- Ambient coordinate order used by the Fourier lemmas. -/
def rackCoordinates (I : Type) (N : ℕ) : KeyCoordinates I N≃ₗ[F] Rack I N where
  toFun x := (keyPlus x,keyMinus x)
  invFun x v := if v.2.1 then x.2 v.1 v.2.2 else x.1 v.1 v.2.2
  left_inv x := by funext v; rcases v with ⟨u,b,i⟩; cases b <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}
def inputCoordinates (p : Shape) (n : ℕ) (I : Type) :
    Vec (I×Block p.g×Fin n)≃ₗ[F] Inputs p n I where
  toFun x i b k:=x (i,b,k)
  invFun x v:=x v.1 v.2.1 v.2.2
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def inputFourierNorm (w : Wgt (Inputs p n I)) : ℝ:=
  fourierNorm (fun x=> w (inputCoordinates p n I x))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}
abbrev NominalAmounts (p : Shape) (q : Format) (d : Rates) (b : Bool) :=
  ∀ i:Messenger q,Digest p.g×Par (d (parcel b i))

def nominalPrinted (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q→ Label p.b) (f : Messenger q→ Flavor p.g) (m : Mixer p n)
    (x : Inputs p n (Messenger q)) : NominalAmounts p q d b :=
  fun i=>(scan p (t i) (f i) (x i),
    role p n (useAtom p (t i) (s i) (f i) (x i)),
    roll (v (parcel b i)) (Tsym m (useAtom p (t i) (s i) (f i) (x i))))

def joinPrinted (a : NominalAmounts p q d b) (r : Messenger q→ F) : Amounts p q d b :=
  fun i=>(a i|>.1,a i|>.2,r i)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K r s0:ℕ}
namespace StatusAnalysis
namespace Quill
variable {q:Format} {d:Rates} {b:Bool} (w:Quill p q d b) (t : Tagging p (Messenger q))
    (z:Messenger q→ F) (m:Mixer p n)
def prelim (K:ℕ) (s:Charts p n d) (i:Messenger q) :=
   d (parcel b i)≤ K^2 ∧ Injective (s (parcel b i)) ∧
   ∀ x,totalRank (s (parcel b i) x)≤ K

def sameInk (i:Messenger q) (v: Magazine p (d (parcel b i))) :=
  Appearance.nearly p (w.amp i).1 (w.amp i).2.1 v

end Quill
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap
open scoped BigOperators
variable {p:Shape} {n N M K s0:ℕ}
namespace StatusAnalysis
variable {q:Format} {d e: Rates} {b:Bool}
abbrev Stalls (p:Shape) := Bool→ Finset (Label p.b)

namespace Fabric
end Fabric
variable {i j:Bool} {L:ℕ}
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function LinearMap Module
open scoped BigOperators Topology
open Template
variable {p : Shape} {N n r K : ℕ}
namespace StatusAnalysis
/-- envelope information to certify a generator, shared l and q. -/
structure Zodiac (p : Shape) where
  l : Tag p.g
  q : F
  s : Bool → Label p.b
  f : Bool→ Flavor p.g

namespace Zodiac
def aspect (w : Zodiac p) (b : Bool) : Appearance p :=
  ⟨w.l,w.s b,w.f b,w.q⟩

def common (w : Zodiac p) := ∀ b,(w.aspect b).apt

end Zodiac
abbrev Terrain (p:Shape) (r:ℕ):= Tag p.g → F → Wgt (Fin r)

abbrev Gazette (p:Shape) (r:ℕ) (d : Rates) :=
   (i:Nodes)→ Appearance p → Fin r→ Wgt (Magazine p (d i))

variable {d e : Rates}
namespace DualAnalysis
def origami (p:Shape) (r:ℕ) (u:Terrain p r) (δ:ℝ) :=
   (∀ i q,IsLaw (u i q)) ∧ ∀ i q,1/2 ≤ pr (u i q) (fun x=>δ ≤ u i q x)

structure reports (p:Shape) (r:ℕ) (u:Terrain p r) (s:Gazette p r d)
    (β δ:ℝ) : Prop where
  law : ∀ i (x:Appearance p),x.apt → ∀ k:Fin r,IsLaw (s i x k)
  supp : ∀ i (x:Appearance p),x.apt →∀ k,carried (s i x k) x.fitsink
  generous : ∀ i (x:Appearance p), x.f=Flavor.full → x.apt →
     ∀ k:Fin r,δ ≤ u x.l x.q k → ∀ v: Par (d i),
       β ≤ pr (s i x k) (fun w=> w.2.1=v)

def playbook (p : Shape) (K : ℕ) := num (Magazine p (K^2) × Magazine p (K^2))

abbrev Scriptum (p:Shape) (d e: Rates) (i : Grid) :=
   Zodiac p × Magazine p (d i.1) × Magazine p (e i.2)

abbrev Touch (p:Shape) (d e : Rates) (i : Grid) := Magazine p (d i.1) × Magazine p (e i.2)

variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
  (η:ℝ)
def couplePage (x:Zodiac p) (i:Grid) :=
    fun j:Fin r=> pairW (s i.1 (x.aspect true) j) (t i.2 (x.aspect false) j)

def circlet (x:Zodiac p) (i:Grid) : Wgt (Touch p d e i) :=
    mixW (u x.l x.q) (couplePage s t x i)

def eligible (x:Zodiac p) (i:Grid) (a : Touch p d e i) :=
    x.common ∧ (x.aspect true).fitsink a.1 ∧ (x.aspect false).fitsink a.2 ∧
      η ≤ circlet u s t x i a

def stellar (A B : Stalls p) : Congress (Scriptum p d e) d e (Label p.b) :=
    fun i=> {
      valid x:= x.1.s true∉ A i.1 ∧ x.1.s false∉ B i.2 ∧ eligible u s t η x.1 i x.2
      writes x:= (x.1.q,x.2.1.2,x.2.2.2)
      addr x:= x.1.s
    }

variable {β δ:ℝ}
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e : Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}
structure RhymeSet (d : ℕ) where
    bit : F
    coal : Cell d
    headBit : F
    gamma : F

def RhymeSet.read {k : ℕ} (s:RhymeSet k) (q:F) (x: Whole k) :=
    s.bit* x.2+ dotProduct s.coal x.1.2+ (s.bit+s.headBit)* x.1.1+s.gamma* q

def RhymeSet.soot {k : ℕ} (s:RhymeSet k) {p:Shape} (x:Appearance p) (y:Magazine p k) :=
    s.read x.q y.2

def leftChime (q:DualCoefficients d e) (i:Grid) : RhymeSet (d i.1) :=
   ⟨q.left i.2,q.north i,q.hed i,0⟩

def rightChime (q:DualCoefficients d e) (i:Grid) : RhymeSet (e i.2) :=
   ⟨q.right i.1,q.south i,q.hed i,q.gam i⟩

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Finset Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}
/-- A fixed positive support gap makes threshold availability exact.
The statement applies to all labels retained for the scalar system. -/
def HasStatusSupportGap (u : Terrain p r) (s : Gazette p r d)
    (t : Gazette p r e) (η : ℝ) : Prop :=
  ∀ (x : Zodiac p),x.common→∀ i y,
    circlet u s t x i y=0 ∨ η≤ circlet u s t x i y

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function Submodule Module LinearMap
open scoped BigOperators
variable {A B J H : Type} [Fintype A] [Fintype B] [Fintype J]
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {d e: Rates} {r K:ℕ}
abbrev Pulsar (p:Shape) (r:ℕ):= Tag p.g → F → Fin r→ F

variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}
def ExactStatusPrediction (u : Terrain p r) (s : Gazette p r d)
    (i : Nodes) (A : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p r) : Prop :=
  ∀ x : Appearance p,x.s∉A→ x.apt→∀ c,0< u x.l x.q c→
    ∀ v,0< s i x c v→ a.soot x v=f x.l x.q c

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset LinearMap Module Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n N K:ℕ} {d:Rates}
def yokeSet {n:ℕ} (w:Cell n) (α:F) : RhymeSet n :=
    ⟨1,w,1+α,0⟩

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {p : Shape} {r : ℕ} {d : Rates}
def SamePrediction (u : Terrain p r) (f g : Pulsar p r) : Prop :=
  ∀ l q c,0< u l q c→ f l q c=g l q c

def ExactCatalog (u : Terrain p r) (s : Gazette p r d)
    (B : ℕ) (f : Nodes→ Pulsar p r) : Prop :=
  ∀ i E,(E.card≤ B)→∀ w α g,
    ExactStatusPrediction u s i E (yokeSet w α) g→ SamePrediction u g (f i)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Module LinearMap
open scoped BigOperators Topology
variable {p:Shape} {r n:ℕ}
namespace StatusAnalysis
namespace DualAnalysis
variable {d e:Rates} {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
open PredictionClass
abbrev styles (d:Rates) := ∀ i:Nodes, Cell (d i)

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {p : Shape} {r : ℕ} {d e : Rates}
def TesterSeparated (u : Terrain p r) (Free : Pulsar p r→ Prop) : Prop :=
  ∀ f g γ,Free f→ Free g→
    SamePrediction u f (fun l q c=> g l q c+γ* q)→γ=0

/-- The seven possible pairs consist of the zero pair and three
nonzero endpoint masks for each of the two second-side predictors. -/
def sevenPredictionPairs (f : Nodes→ Pulsar p r) : Finset (Nodes→ Pulsar p r) := by
  classical
  exact {0} ∪ (univ.image fun j : Nodes=> fun i=> if i then f j else 0) ∪
    (univ.image fun j : Nodes=> fun i=> if i then 0 else f j) ∪
    (univ.image fun j : Nodes=> fun _=> f j)

def ExactAnnounced (u : Terrain p r) (s : Gazette p r d)
    (cat : Nodes→ Pulsar p r) (B : ℕ) : Prop :=
  ∃ f∈sevenPredictionPairs cat,∃ w : styles d,∃ α : Party,∃ E : Stalls p,
    ∀ i,(E i).card≤ B ∧ ExactStatusPrediction u s i (E i) (yokeSet (w i) (α i)) (f i)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
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
  ∀ x : Appearance p,x.s∉A→ x.apt→ x.f=Flavor.full→∀ c,0< u x.l x.q c→
    ∀ v,0< s i x c v→ a.soot x v=f x.l x.q c

def GenericStatusContinuation (u : Terrain p r) (s : Gazette p r d) (B : ℕ) : Prop :=
  ∀ i E,E.card≤ B→∀ a f,GenericStatusPrediction u s i E a f→
    ExactStatusPrediction u s i ∅ a f

def genericStellar (u : Terrain p r) (s : Gazette p r d) (t : Gazette p r e)
    (η : ℝ) (A B : Stalls p) : Congress (Scriptum p d e) d e (Label p.b) :=
  fun i=>{stellar u s t η A B i with
    valid x:=(stellar u s t η A B i).valid x ∧ ∀ side,x.1.f side=Flavor.full}

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Module Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q A B T : Type} [AddCommGroup V] [Module F V]
/-- The cells are precisely the fibers of one linear map. Merely being
a function of linear coordinates would permit arbitrary coarsenings. -/
def HasFullLinearCells (f : Q→ V→ A) (R : ℕ) : Prop :=
  ∃ r : ℕ,r≤ R ∧ ∃ L : V→ₗ[F]Vec (Fin r),
    ∀ q x y,f q x=f q y ↔ L x=L y

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
noncomputable section
abbrev QField := ZMod 2

variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
abbrev Hyperbolic (h : ℕ) := (Fin h→ QField)×(Fin h→ QField)

def hyperbolicQuadratic (h : ℕ) : QuadraticForm QField (Hyperbolic h) :=
  LinearMap.BilinMap.toQuadraticMap
    ((dotProductBilin QField QField : (Fin h→ QField)→ₗ[QField]
      (Fin h→ QField)→ₗ[QField] QField).compl₁₂
      (LinearMap.fst QField _ _) (LinearMap.snd QField _ _))

theorem hyperbolic_apply (h : ℕ) (v : Hyperbolic h) :
    hyperbolicQuadratic h v=dotProduct v.1 v.2 := rfl

theorem hyperbolic_polar (h : ℕ) (v w : Hyperbolic h) :
    (hyperbolicQuadratic h).polarBilin v w=dotProduct v.1 w.2+dotProduct w.1 v.2 := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  simp only [hyperbolic_apply,Prod.fst_add,Prod.snd_add,add_dotProduct,dotProduct_add]
  ring

theorem hyperbolic_nondegenerate (h : ℕ) :
    (hyperbolicQuadratic h).polarBilin.Nondegenerate := by
  constructor
  · intro v hv
    apply Prod.ext
    · funext i
      have hi := hv (0,Pi.single i 1)
      change (hyperbolicQuadratic h).polarBilin v (0,Pi.single i 1)=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi
    · funext i
      have hi := hv (Pi.single i 1,0)
      change (hyperbolicQuadratic h).polarBilin v (Pi.single i 1,0)=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi
  · intro v hv
    apply Prod.ext
    · funext i
      have hi := hv (0,Pi.single i 1)
      change (hyperbolicQuadratic h).polarBilin (0,Pi.single i 1) v=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi
    · funext i
      have hi := hv (Pi.single i 1,0)
      change (hyperbolicQuadratic h).polarBilin (Pi.single i 1,0) v=0 at hi
      rw [hyperbolic_polar] at hi
      simpa using hi

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev HyperbolicIdx (h : ℕ) := Fin h⊕Fin h

/-- An ordered matrix representative: its symmetric part is the polar
form, whereas the matrix itself retains the quadratic values. -/
def hyperbolicMatrix (h : ℕ) : Matrix (HyperbolicIdx h) (HyperbolicIdx h) QField :=
  Matrix.fromBlocks 0 1 0 0

def hyperbolicCoordinates (h : ℕ) :
    (HyperbolicIdx h→ QField)≃ₗ[QField]Hyperbolic h :=
  LinearEquiv.sumArrowLequivProdArrow _ _ _ _

theorem hyperbolic_matrix_apply (h : ℕ) (v : HyperbolicIdx h→ QField) :
    (hyperbolicMatrix h).toQuadraticForm' v=
      hyperbolicQuadratic h (hyperbolicCoordinates h v) := by
  change Matrix.toBilin' (hyperbolicMatrix h) v v=_
  rw [Matrix.toBilin'_apply',hyperbolic_apply]
  change dotProduct v (hyperbolicMatrix h*ᵥv)=dotProduct (v∘Sum.inl) (v∘Sum.inr)
  simp only [hyperbolicMatrix,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,
    Matrix.one_mulVec,zero_add,add_zero]
  rw [show v=Sum.elim (v∘Sum.inl) (v∘Sum.inr) from by ext i; cases i <;> rfl]
  simp only [sumElim_dotProduct_sumElim,dotProduct_zero,add_zero]
  rfl

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Submodule Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
theorem linear_image_dimension_growth {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V]
    (f : V→ₗ[F]W) (S T : Space V) (hST : S≤ T) :
    dim (T.map f)-dim (S.map f)≤ dim T-dim S := by
  let fS:=f.comp S.subtype
  let fT:=f.comp T.subtype
  let g : fS.ker→ₗ[F]fT.ker:=
    ((Submodule.inclusion hST).comp fS.ker.subtype).codRestrict fT.ker (fun x=> x.property)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fT.ker=>(z.val:V)) h
  have hk:=LinearMap.finrank_le_finrank_of_injective hg
  have hs:=fS.finrank_range_add_finrank_ker
  have ht:=fT.finrank_range_add_finrank_ker
  have hrS : fS.range=S.map f := by rw [LinearMap.range_comp,Submodule.range_subtype]
  have hrT : fT.range=T.map f := by rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [hrS] at hs
  rw [hrT] at ht
  have hm:=Submodule.finrank_mono hST
  change dim fS.ker≤ dim fT.ker at hk
  change dim (S.map f)+dim fS.ker=dim S at hs
  change dim (T.map f)+dim fT.ker=dim T at ht
  omega

variable {I : Type} [Fintype I] {V : I→ Type}
  [∀ i,AddCommGroup (V i)] [∀ i,Module F (V i)]
/-- Close a pin space under the coordinate block projections. -/
def blockClosure (S : Space (∀ i,V i)) : Space (∀ i,V i) :=
  Submodule.pi Set.univ (fun i=> S.map (LinearMap.proj i))

omit [Fintype I] in
theorem le_blockClosure (S : Space (∀ i,V i)) : S≤ blockClosure S := by
  intro x hx
  exact Submodule.mem_pi.mpr (fun i _=>⟨x,hx,rfl⟩)

omit [Fintype I] in
theorem blockClosure_projection (S : Space (∀ i,V i)) (i : I) :
    (blockClosure S).map (LinearMap.proj i)=S.map (LinearMap.proj i) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (Submodule.mem_pi.mp hx) i (Set.mem_univ i)
  · exact Submodule.map_mono (le_blockClosure S)

omit [Fintype I] in
theorem blockClosure_idempotent (S : Space (∀ i,V i)) :
    blockClosure (blockClosure S)=blockClosure S := by
  unfold blockClosure
  congr 1
  funext i
  exact blockClosure_projection S i

def blockClosureEquiv (S : Space (∀ i,V i)) :
    blockClosure S≃ₗ[F](∀ i,S.map (LinearMap.proj i)) where
  toFun x i:=⟨x.val i,(Submodule.mem_pi.mp x.property) i (Set.mem_univ i)⟩
  invFun x:=⟨fun i=>(x i).val,Submodule.mem_pi.mpr (fun i _=>(x i).property)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

variable [∀ i,FiniteDimensional F (V i)]
theorem blockClosure_dimension (S : Space (∀ i,V i)) :
    dim (blockClosure S)=∑ i,dim (S.map (LinearMap.proj i)) := by
  unfold dim
  rw [(blockClosureEquiv S).finrank_eq]
  exact Module.finrank_pi_fintype F

/-- Closing a new t-dimensional extension of an already closed pin space
adds at most one copy of t for each coordinate block. -/
theorem blockClosure_dimension_step (S T : Space (∀ i,V i)) (hST : S≤ T)
    (hS : blockClosure S=S) :
    dim (blockClosure T)-dim S≤ Fintype.card I*(dim T-dim S) := by
  have h (i : I) : dim (T.map (LinearMap.proj i))≤
      dim (S.map (LinearMap.proj i))+(dim T-dim S) := by
    have hi:=linear_image_dimension_growth (LinearMap.proj i) S T hST
    omega
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=> h i)
  rw [Finset.sum_add_distrib,←blockClosure_dimension,←blockClosure_dimension,hS] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  omega

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev ImagePlan (C I : Type) := C→ Space (Vec I)

def imagePlanRank {C I : Type} [Fintype C] [Fintype I] (P : ImagePlan C I) :=∑ e,dim (P e)

structure ImagePin (C I : Type) (N : ℕ) where
  sp : ImagePlan C I
  target : C→ Mat (Fin N) I

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}
def imagePinAgree (X : A→ C→ Mat (Fin N) I) (P : ImagePin C I N) (x : A) :=
  ∀ e,∀ v∈P.sp e,X x e*ᵥv=P.target e*ᵥv

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}
def imagePinClear (X : A→ C→ Mat (Fin N) I) (a : ImagePin C I N) (ζ : ℝ) (w : Wgt A) :=
  ∀ b : ImagePin C I N,pr w (imagePinAgree X b)≤
    fee N ζ (imagePlanRank (a.sp⊔b.sp)-imagePlanRank a.sp)

structure ImageClosure (C I : Type) [Fintype C] [Fintype I] (c : ℕ) where
  close : ImagePlan C I→ ImagePlan C I
  extensive : ∀ P,P≤ close P
  idempotent : ∀ P,close (close P)=close P
  growth : ∀ P Q,P≤ Q→ close P=P→
    imagePlanRank (close Q)-imagePlanRank P≤ c*(imagePlanRank Q-imagePlanRank P)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}
abbrev ImageCross (C I : Type) := C→ Mat I I

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N c : ℕ}
def imageDustPin : ImagePin C I N:=⟨⊥,0⟩

structure ImageRipe (X : A→ C→ Mat (Fin N) I) (cl : ImageClosure C I c)
    (w μ : Wgt A) (S : Finset A) (a : ImagePin C I N) (D ζ : ℝ) (K : ℕ) : Prop where
  pos : 0< partMass w S
  fixpin : ∀ x∈S,imagePinAgree X a x
  closed : cl.close a.sp=a.sp
  bound : imagePlanRank a.sp≤ K
  clear : imagePinClear X a ζ (partW w S)
  density x : partW w S x≤ bp (D* N)*μ x

structure ImageLeafMixture (A C I : Type) [Fintype C] [Fintype I] (N : ℕ) where
  T : Tiles A
  pin : Finset A→ ImagePin C I N

namespace ImageLeafMixture
variable (s : ImageLeafMixture A C I N)
def poller (x : A) : ImagePin C I N:=
  open scoped Classical in
  if h : inTiles s.T x then s.pin h.choose else imageDustPin

def rooting (x : A):=(s.poller x).sp

def amount (w : Wgt A):=allMass w s.T

def sap (w : Wgt A):=allW w s.T

def within (P : A→ Prop):=∀ i∈s.T,∀ x∈i,P x

structure strength (X : A→ C→ Mat (Fin N) I) (cl : ImageClosure C I c)
    (w μ : Wgt A) (D ζ : ℝ) (K : ℕ) : Prop where
  part : apart s.T
  leaf : ∀ i∈s.T,ImageRipe X cl w μ i (s.pin i) D ζ K

variable {s} {X : A→ C→ Mat (Fin N) I} {cl : ImageClosure C I c}
  {w μ : Wgt A} {D ζ : ℝ} {K : ℕ}
end ImageLeafMixture
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section
namespace IndependentClub
variable {L I S X Y : Type} [DecidableEq L] [DecidableEq I] [Fintype S]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable (C : Club I X L) (U : Bool → Space (Vec S)) (v : Bool → I → Vec S)
def bundle (p : Finset I) (s : Straps L) : Prop :=
  (∀ i∈p,C.zone s i) ∧ ∀ b,LinearIndepOn F ((U b).mkQ ∘ v b) (p : Set I)

def length3 (s : Straps L) (π : X →ₗ[F] Y) (x : X) : Prop :=
  ∃ p : Finset I,bundle C U v p s ∧ p.card ≤ 3 ∧ C.contents p=x ∧ π x=0

def ration (s : Straps L) (π : X →ₗ[F] Y) : Space X :=
  Submodule.span F (length3 C U v s π)

end IndependentClub
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section
namespace IndependentClub
variable {L I S X Y : Type} [DecidableEq L] [DecidableEq I] [Fintype S]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable (C : Club I X L) (U : Bool → Space (Vec S)) (v : Bool → I → Vec S)
def enlarge (p : Finset I) (b : Bool) : Space (Vec S) :=
  U b ⊔ Submodule.span F (v b '' (p : Set I))

variable [Module.Finite F X]
end IndependentClub
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B R V : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup R] [Module QField R] [AddCommGroup V] [Module QField V]
def quadraticFramesAt (q : QuadraticForm QField V) (C : QuadraticForm QField B→ Prop)
    (P : B→ₗ[QField]V) := Function.Injective P ∧ C (q.comp P)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B C V R : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup C] [Module QField C] [AddCommGroup V] [Module QField V]
  [AddCommGroup R] [Module QField R]
/-- The three stored blocks are one primal block and the two channel blocks. -/
abbrev QuadraticFull (B C : Type) := B×(C×C)

def quadraticPrimalIn : B→ₗ[QField]QuadraticFull B C:=LinearMap.inl QField _ _

def quadraticXIn : C→ₗ[QField]QuadraticFull B C:=
  (LinearMap.inr QField _ _).comp (LinearMap.inl QField _ _)

def quadraticYIn : C→ₗ[QField]QuadraticFull B C:=
  (LinearMap.inr QField _ _).comp (LinearMap.inr QField _ _)

/-- Exactly the proposed own-frame conditions: a prescribed quadratic form
on the primal image and polar orthogonality of X to that image. Y is free. -/
def quadraticChannelClass (Q : QuadraticForm QField B)
    (A : QuadraticForm QField (QuadraticFull B C)) : Prop :=
  A.comp quadraticPrimalIn=Q ∧
    ∀ (c : C) (b : B),A.polarBilin (quadraticXIn c) (quadraticPrimalIn b)=0

def quadraticChannelValid (q : QuadraticForm QField V) (Q : QuadraticForm QField B)
    (P : QuadraticFull B C→ₗ[QField]V) :=
  quadraticFramesAt q (quadraticChannelClass Q) P

def quadraticChannelRaw [Fintype (QuadraticFull B C→ₗ[QField]V)]
    (q : QuadraticForm QField V) (Q : QuadraticForm QField B) :
    Wgt (QuadraticFull B C→ₗ[QField]V):=unifOn (quadraticChannelValid q Q)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module LinearMap
noncomputable section
variable {I : Type} [Fintype I]
/-- Squares in a subspace, over the binary field. -/
def quadraticSquares (S : Space (Vec I)) : Space (Mat I I) :=
  Submodule.span F {W | ∃ x∈S,W=vecMulVec x x}

def quadraticCross (K : Space (Vec I)) : Space (Mat I I) :=
  Submodule.span F {W | ∃ k∈K,∃ b,W=vecMulVec k b+vecMulVec b k}

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A J : Type} [Fintype I] [Fintype A] [Fintype J]
/-- A single primal map acts on both factors of a moment. -/
def quadraticMomentMap (P : Vec I→ₗ[F]Vec A) : Mat I I→ₗ[F]Mat A A := by
  classical
  exact liftM (LinearMap.toMatrix' P) (LinearMap.toMatrix' P)

theorem quadratic_moment_injective (P : Vec I→ₗ[F]Vec A)
    (hP : Function.Injective P) : Function.Injective (quadraticMomentMap P) := by
  classical
  have hi : Function.Injective (LinearMap.toMatrix' P).mulVec := by
    intro x y he
    exact hP (by simpa only [LinearMap.toMatrix'_mulVec] using he)
  exact liftM_inj hi hi

/-- The ordered product of two polar channel evaluations. Its matrix is
used only as a representative of a quadratic functional. -/
def quadraticChannelBilin (q : QuadraticForm F (Vec A))
    (X Y : J→ Vec A) : LinearMap.BilinForm F (Vec A) :=
  ∑ j,(q.polarBilin (X j)).smulRight (q.polarBilin (Y j))

def quadraticChannelFunctional (q : QuadraticForm F (Vec A))
    (X Y : J→ Vec A) : Mat A A→ₗ[F]F := by
  classical
  exact mpair (quadraticChannelBilin q X Y).toMatrix'

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
theorem matrix_quadratic_comp {I A : Type} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] (E : Mat A A) (P : Vec I→ₗ[F]Vec A) :
    E.toQuadraticForm'.comp P=
      (pullM (LinearMap.toMatrix' P) (LinearMap.toMatrix' P) E).toQuadraticForm' := by
  apply QuadraticMap.ext
  intro x
  change Matrix.toBilin' E (P x) (P x)=
    Matrix.toBilin' (pullM (LinearMap.toMatrix' P) (LinearMap.toMatrix' P) E) x x
  simp only [Matrix.toBilin'_apply']
  simpa only [evmat,LinearMap.toMatrix'_mulVec] using
    (evmat_pull (LinearMap.toMatrix' P) (LinearMap.toMatrix' P) E x x).symm

variable {I : Type} [Fintype I] [DecidableEq I]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]
/-- A hyperbolic channel map of small image has an ordered quadratic
matrix representative of at most the same rank. -/
theorem hyperbolic_matrix_representative (h : ℕ) (g : Vec I→ₗ[F]Hyperbolic h) :
    ∃ M : Mat I I,(∀ v,M.toQuadraticForm' v=hyperbolicQuadratic h (g v)) ∧
      M.rank≤ rk g := by
  let L:=(hyperbolicCoordinates h).symm.toLinearMap.comp g
  let A:=LinearMap.toMatrix' L
  refine ⟨pullM A A (hyperbolicMatrix h),?_,?_⟩
  · intro v
    rw [←matrix_quadratic_comp,QuadraticMap.comp_apply,hyperbolic_matrix_apply]
    exact congrArg (hyperbolicQuadratic h) ((hyperbolicCoordinates h).apply_symm_apply (g v))
  · rw [pullM_def]
    exact (Matrix.rank_mul_le_right ..).trans (by
      change A.rank≤ rk g
      rw [rank_cast,toMat_map]
      exact rk_comp_le_right g (hyperbolicCoordinates h).symm.toLinearMap)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
def selectedAtComponent (l : I→ Tag p.g) (s : I→ Label p.b) (z : I→ Base p.g n)
    (e : Comp p.g) : Space (Ray p n) :=
  Submodule.span F {v | ∃ i,inc e (l i) ∧ v=point p (s i) (z i)}

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {D B : Type} [Fintype D] [Fintype B] [DecidableEq B]
def jointProjection (b : B) : Vec (D×B)→ₗ[F]Vec D where
  toFun v d:=v (d,b)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def jointInjection (b : B) : Vec D→ₗ[F]Vec (D×B) where
  toFun v x:=if x.2=b then v x.1 else 0
  map_add' _ _:=by ext x; by_cases h : x.2=b <;> simp [h]
  map_smul' _ _:=by ext x; by_cases h : x.2=b <;> simp [h]

def jointSpace (P : B→ Space (Vec D)) : Space (Vec (D×B)) where
  carrier:={v | ∀ b,jointProjection b v∈P b}
  add_mem' hx hy b:= (P b).add_mem (hx b) (hy b)
  zero_mem' b:=(P b).zero_mem
  smul_mem' c x hx b:=(P b).smul_mem c (hx b)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev JointRay (p : Shape) (n : ℕ) := Vec (Row p n×Bool)

abbrev JointMoment (p : Shape) (n : ℕ) := Mat (Row p n×Bool) (Row p n×Bool)

abbrev JointProfile (p : Shape) (n : ℕ) := Comp p.g→ JointMoment p n

def jointCutEmbed {p : Shape} {n : ℕ} (x : Bool→ Profile p n) : JointProfile p n :=
  fun e=> blockDiagonal (fun i=> x i e)

variable {p : Shape} {n : ℕ} {I : Bool→ Type}
  [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
/-- Only symmetric supported Gram characters are fixed. This is precisely
quadratic Gram information, without specifying ordered pairings. -/
def quadraticTraced (E : Rail I) (Z : Mat I I) (x : KeyCoordinates I N) : Prop:=
  ∀ M : Mat I I,Mᵀ=M → withinRail M E → gramPrimitive M x=mpair M Z

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]
def geoMatrix (g : Route I G) (A : GeoM g) : Mat I I:=
  fun i j=> if h:g i=g j then A (g i) ⟨i,rfl⟩ ⟨j,h.symm⟩ else 0

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- N is half the ambient dimension. The primal frame is stored once. -/
abbrev OneFrame (p : Shape) (n N : ℕ) :=
  QuadraticFull (Ray p n) (Vec (Fin p.h))→ₗ[F]Vec (HyperbolicIdx N)

abbrev OneOrient (p : Shape) (n N : ℕ) := Comp p.g→ OneFrame p n N

abbrev OneAmbient (p : Shape) (N : ℕ) :=
  Comp p.g→ Mat (HyperbolicIdx N) (HyperbolicIdx N)

variable {p : Shape} {n N : ℕ}
def oneFrameLaw (m : Mixer p n) (o : OneOrient p n N) : Prop :=
  ∀ e,quadraticChannelValid (hyperbolicMatrix N).toQuadraticForm'
    (selfM p n m.mixM).toQuadraticForm' (o e)

def onePrimal (P : OneFrame p n N) : Ray p n→ₗ[F]Vec (HyperbolicIdx N) :=
  P.comp quadraticPrimalIn

def oneChannelX (P : OneFrame p n N) (j : Fin p.h) :=
  P (quadraticXIn (Pi.single j 1))

def oneChannelY (P : OneFrame p n N) (j : Fin p.h) :=
  P (quadraticYIn (Pi.single j 1))

def oneMomentEmbed (o : OneOrient p n N) : Profile p n→ₗ[F]OneAmbient p N where
  toFun x e:=quadraticMomentMap (onePrimal (o e)) (x e)
  map_add' x y:=by ext e i j; simp only [Pi.add_apply,map_add,Matrix.add_apply]
  map_smul' c x:=by ext e i j; simp only [Pi.smul_apply,map_smul,RingHom.id_apply,
    Matrix.smul_apply]

def oneFunctional (o : OneOrient p n N) : OneAmbient p N→ₗ[F]F where
  toFun x:=∑ e,quadraticChannelFunctional (hyperbolicMatrix N).toQuadraticForm'
    (oneChannelX (o e)) (oneChannelY (o e)) (x e)
  map_add' x y:=by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c x:=by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,
    Finset.smul_sum]

theorem one_primal_injective {m : Mixer p n} {o : OneOrient p n N}
    (ho : oneFrameLaw m o) (e : Comp p.g) : Function.Injective (onePrimal (o e)) := by
  intro x y he
  exact congrArg Prod.fst ((ho e).1 he)

theorem one_moment_injective {m : Mixer p n} {o : OneOrient p n N}
    (ho : oneFrameLaw m o) : Function.Injective (oneMomentEmbed o) := by
  intro x y he
  funext e
  exact quadratic_moment_injective _ (one_primal_injective ho e) (congrFun he e)

/-- The hole definition uses the new single-frame embedding and functional. -/
def oneHole (m : Mixer p n) (x y : OneOrient p n N) : Prop :=
  oneFrameLaw m x ∧ oneFrameLaw m y ∧ ∃ v w : Profile p n,
    v∈Xspace p n ∧ w∈Xspace p n ∧
    oneMomentEmbed x v=oneMomentEmbed y w ∧
    (∀ i∈Xspace p n,oneFunctional y (oneMomentEmbed x i)=grad m v i) ∧
    (∀ i∈Xspace p n,oneFunctional x (oneMomentEmbed y i)=grad m w i) ∧
    role p n v+role p n w=1

theorem one_hole_sym {m : Mixer p n} {x y : OneOrient p n N}
    (h : oneHole m x y) : oneHole m y x := by
  obtain ⟨hx,hy,v,w,hv,hw,he,h,g,hp⟩:=h
  exact ⟨hy,hx,w,v,hw,hv,he.symm,g,h,(add_comm _ _).trans hp⟩

theorem one_hole_irrefl (m : Mixer p n) (x : OneOrient p n N) : ¬oneHole m x x := by
  rintro ⟨hx,_,v,w,_,_,he,_,_,hp⟩
  rw [one_moment_injective hx he,char_two] at hp
  exact zero_ne_one hp

theorem one_hole_triangle {m : Mixer p n} {x y z : OneOrient p n N}
    (h1 : oneHole m x y) (h2 : oneHole m y z) : ¬oneHole m x z := by
  intro h3
  obtain ⟨_,_,a,b,ha,hb,hab,u1,u2,p1⟩:=h1
  obtain ⟨_,_,c,d,hc,hd,hcd,u3,u4,p2⟩:=h2
  obtain ⟨_,_,e,f,he,hf,hef,u5,u6,p3⟩:=h3
  have hx : grad m b c=grad m f d := by rw [←u2 _ hc,←u6 _ hd,hcd]
  have hy : grad m a e=grad m d f := by rw [←u1 _ he,←u4 _ hf,hef]
  have hz : grad m e a=grad m c b := by rw [←u5 _ ha,←u3 _ hb,hab]
  simp only [grad_val] at hx hy hz
  let A:=role p n
  let T:=Tsym m
  have cancel (x y : F) (he : x=y) : x+y=0 := by rw [he,char_two]
  have ht (u v) : T u v+T v u=0:=cancel _ _ (T_swap m _ _)
  have hp : (A a+A b)+(A c+A d)+(A e+A f)=0 := by
    change A _+T _ _=A _+T _ _ at hx hy hz
    calc
      (A a+A b)+(A c+A d)+(A e+A f)
        = ((A c+T b c)+(A d+T f d))+
          ((A e+T a e)+(A f+T d f))+
          ((A a+T e a)+(A b+T c b)) := by
            symm
            calc
              _ = ((A a+A b)+(A c+A d)+(A e+A f))+
                (T b c+T c b)+(T f d+T d f)+(T a e+T e a) := by ac_rfl
              _ = _ := by simp only [ht,add_zero]
      _ = 0 := by rw [cancel _ _ hx,cancel _ _ hy,cancel _ _ hz]; simp
  unfold A at hp
  rw [p1,p2,p3,char_two,zero_add] at hp
  exact one_ne_zero hp

def oneRawHoles (m : Mixer p n) : Holes (OneOrient p n N) where
  rel:=oneHole m
  sym:=one_hole_sym
  irr:=one_hole_irrefl m
  ntri:=one_hole_triangle

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
instance oneFrameFintype (p : Shape) (n N : ℕ) : Fintype (OneFrame p n N) := by
  classical
  letI : Fintype (QuadraticFull (Ray p n) (Vec (Fin p.h))):=inferInstance
  letI : Fintype (Vec (HyperbolicIdx N)):=inferInstance
  exact Fintype.ofInjective (fun f : OneFrame p n N=>⇑f) DFunLike.coe_injective

instance oneOrientFintype (p : Shape) (n N : ℕ) : Fintype (OneOrient p n N) :=
  inferInstanceAs (Fintype (Comp p.g→ OneFrame p n N))

/-- The new raw law samples independent, uniformly distributed single frames
at the cycle components. The own X-channel constraints are part of its support. -/
def oneRaw (m : Mixer p n) (N : ℕ) : Wgt (OneOrient p n N) := by
  classical
  exact prodW (fun _ : Comp p.g=> quadraticChannelRaw (C:=Vec (Fin p.h))
    (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
abbrev UnitChannels (h : ℕ) := Bool→ Hyperbolic h

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}
def jointCutMap : (Bool→ Profile p n)→ₗ[F]JointProfile p n where
  toFun:=jointCutEmbed
  map_add' x y:=by
    funext e
    exact Matrix.blockDiagonal_add _ _
  map_smul' c x:=by
    funext e
    exact Matrix.blockDiagonal_smul c _

def jointXspace : Space (JointProfile p n) :=
  (Submodule.pi Set.univ (fun _ : Bool=> Xspace p n)).map jointCutMap

def jointEndpointMap (i : Bool) : Profile p n→ₗ[F]JointProfile p n :=
  jointCutMap.comp (LinearMap.single F (fun _ : Bool=> Profile p n) i)

def jointMatrixFunctional (M : JointProfile p n) : JointProfile p n→ₗ[F]F :=
  ∑ e,(mpair (M e)).comp (LinearMap.proj e)

def jointQuadraticConstraints (P K : Comp p.g→ Space (JointRay p n)) :
    Space (JointProfile p n) :=
  Submodule.pi Set.univ (fun e=> quadraticSquares (P e)⊔quadraticCross (K e))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}
def jointCompressionRank (p : Shape) (f r : ℕ) : ℕ:=2* drow p (2* f) (2* r)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}
def frozenChannelKernel {I : Type} [Fintype I] (h : ℕ) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F]Hyperbolic h) : Space (Vec I) :=
  (C.comap g₀).map P.subtype

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev OneUnit (p : Shape) (n N : ℕ) := Bool→ OneOrient p n N

abbrev OneUnitFull (p : Shape) (n : ℕ) := JointRay p n×UnitChannels p.h

variable {p : Shape} {n N : ℕ}
def oneUnitMap (x : OneUnit p n N) (e : Comp p.g) :
    OneUnitFull p n→ₗ[F]Vec (HyperbolicIdx N) :=
  ∑ i,(x i e).comp
    (((jointProjection i).comp (LinearMap.fst F _ _)).prod
      ((LinearMap.proj i).comp (LinearMap.snd F _ _)))

def oneUnitActual (x y : OneUnit p n N) (e : Comp p.g) :
    OneUnitFull p n→ₗ[F]OneUnitFull p n→ₗ[F]F :=
  (hyperbolicMatrix N).toQuadraticForm'.polarBilin.compl₁₂ (oneUnitMap x e) (oneUnitMap y e)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]
abbrev OneKeys (t : Tagging p I) (N : ℕ) := ∀ a,TagStar (t a)→ Vec (HyperbolicIdx N)

def oneVolleyKeys (v : Volley p n I) (t : Tagging p I) (x : OneUnit p n N) : OneKeys t N :=
  fun a e=> onePrimal (x (v.obj a) e.val) (v.rayAt a)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] {V : J→ Type}
  [∀ j,AddCommGroup (V j)] [∀ j,Module F (V j)] [∀ j,FiniteDimensional F (V j)]
def coordinateClosure (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) : Space (Vec I) :=
  (blockClosure (P.map E.toLinearMap)).map E.symm.toLinearMap

theorem coordinate_closure_map (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) :
    (coordinateClosure E P).map E.toLinearMap=blockClosure (P.map E.toLinearMap) := by
  rw [coordinateClosure,←Submodule.map_comp]
  simp

theorem le_coordinate_closure (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) :
    P≤ coordinateClosure E P := by
  intro v hv
  exact ⟨E v,le_blockClosure _ ⟨v,hv,rfl⟩,E.symm_apply_apply v⟩

theorem coordinate_closure_idempotent (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) :
    coordinateClosure E (coordinateClosure E P)=coordinateClosure E P := by
  change (blockClosure ((coordinateClosure E P).map E.toLinearMap)).map E.symm.toLinearMap=_
  rw [coordinate_closure_map,blockClosure_idempotent]
  rfl

theorem coordinate_closure_growth (E : Vec I≃ₗ[F](∀ j,V j)) (P Q : Space (Vec I))
    (hPQ : P≤ Q) (hP : coordinateClosure E P=P) :
    dim (coordinateClosure E Q)-dim P≤ Fintype.card J*(dim Q-dim P) := by
  have hp : blockClosure (P.map E.toLinearMap)=P.map E.toLinearMap :=
    (coordinate_closure_map E P).symm.trans (congrArg (Submodule.map E.toLinearMap) hP)
  have h:=blockClosure_dimension_step (P.map E.toLinearMap) (Q.map E.toLinearMap)
    (Submodule.map_mono hPQ) hp
  have he : dim (coordinateClosure E Q)=dim (blockClosure (Q.map E.toLinearMap)):=
    E.symm.finrank_map_eq _
  change dim (blockClosure (Q.map E.toLinearMap))-dim (P.map E.toLinearMap)≤
    Fintype.card J*(dim (Q.map E.toLinearMap)-dim (P.map E.toLinearMap)) at h
  rw [he]
  simpa only [dim,LinearEquiv.finrank_map_eq] using h

variable {C : Type} [Fintype C]
/-- Closing every component under the same coordinate blocks has the
same closure factor; the number of components does not inflate it. -/
def coordinateImageClosure (E : Vec I≃ₗ[F](∀ j,V j)) : ImageClosure C I (Fintype.card J) where
  close P e:=coordinateClosure E (P e)
  extensive P e:=le_coordinate_closure E (P e)
  idempotent P:=funext (fun e=> coordinate_closure_idempotent E (P e))
  growth P Q hPQ hP:=by
    have hg (e : C) : dim (coordinateClosure E (Q e))≤
        dim (P e)+Fintype.card J*(dim (Q e)-dim (P e)) := by
      have h:=coordinate_closure_growth E (P e) (Q e) (hPQ e) (congrFun hP e)
      omega
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=> hg e)
    rw [Finset.sum_add_distrib,←Finset.mul_sum] at hh
    have hd : (∑ e,(dim (Q e)-dim (P e)))=imagePlanRank Q-imagePlanRank P := by
      rw [imagePlanRank,imagePlanRank,Finset.sum_tsub_distrib]
      exact fun e _=> Submodule.finrank_mono (hPQ e)
    rw [hd] at hh
    change imagePlanRank (fun e=> coordinateClosure E (Q e))≤
      imagePlanRank P+Fintype.card J*(imagePlanRank Q-imagePlanRank P) at hh
    omega

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev OneBlock := Bool⊕(Bool⊕Bool)

def oneBlockSlots (p : Shape) (n : ℕ) : OneBlock→ Type
  | Sum.inl _=> Row p n
  | Sum.inr _=> Fin p.h

instance oneBlockSlotsFintype (p : Shape) (n : ℕ) (b : OneBlock) : Fintype (oneBlockSlots p n b) := by
  cases b <;> dsimp only [oneBlockSlots] <;> infer_instance

instance oneBlockSlotsDecidable (p : Shape) (n : ℕ) (b : OneBlock) : DecidableEq (oneBlockSlots p n b) := by
  cases b <;> dsimp only [oneBlockSlots] <;> infer_instance

abbrev OneColumn (p : Shape) (n : ℕ) := Σ b : OneBlock,oneBlockSlots p n b

def oneBlockCoordinates (p : Shape) (n : ℕ) :
    Vec (OneColumn p n)≃ₗ[F](∀ b : OneBlock,Vec (oneBlockSlots p n b)) where
  toFun v b i:=v ⟨b,i⟩
  invFun v i:=v i.1 i.2
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def oneNominalCoordinates (p : Shape) (n : ℕ) : Vec (OneColumn p n)≃ₗ[F]OneUnitFull p n where
  toFun v:=(fun ri=> v ⟨Sum.inl ri.2,ri.1⟩,
    fun i=>(fun j=> v ⟨Sum.inr (Sum.inl i),j⟩,fun j=> v ⟨Sum.inr (Sum.inr i),j⟩))
  invFun v k:=match k with
    | ⟨Sum.inl i,r⟩=> v.1 (r,i)
    | ⟨Sum.inr (Sum.inl i),j⟩=>((v.2 i).1) j
    | ⟨Sum.inr (Sum.inr i),j⟩=>((v.2 i).2) j
  left_inv v:=by
    funext k
    rcases k with ⟨i,k⟩
    rcases i with i|i
    · rfl
    · cases i <;> rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def oneAmbientCoordinates (N : ℕ) : Vec (HyperbolicIdx N)≃ₗ[F]Vec (Fin (2* N)) :=
  LinearEquiv.funCongrLeft F F
    (finSumFinEquiv.trans (finCongr (Nat.two_mul N).symm)).symm

def oneCoordinateImages {p : Shape} {n N : ℕ} (x : OneUnit p n N) (e : Comp p.g) :
    Mat (Fin (2* N)) (OneColumn p n) :=
  LinearMap.toMatrix' ((oneAmbientCoordinates N).toLinearMap.comp
    ((oneUnitMap x e).comp (oneNominalCoordinates p n).toLinearMap))

/-- The actual one-frame nominal columns split into P1, P2, X1, X2, Y1,
Y2. The resulting closure factor is exactly six. -/
def onePinClosure (p : Shape) (n : ℕ) : ImageClosure (Comp p.g) (OneColumn p n) 6 := by
  have hc : Fintype.card OneBlock=6:=by simp [OneBlock]
  exact hc ▸ coordinateImageClosure (oneBlockCoordinates p n)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev OneFull (p : Shape) (n : ℕ) := QuadraticFull (Ray p n) (Vec (Fin p.h))

variable {p : Shape} {n N : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneUnitRaw (m : Mixer p n) (N : ℕ) : Wgt (OneUnit p n N) :=
  prodW (fun _ : Bool=> oneRaw m N)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]
  {p : Shape} {n N : ℕ}
def oneScatter (t : Tagging p I) (N : ℕ) : OneKeys t N ≃ Rack (KeySlots p t) N where
  toFun x:=(fun a i=> x i.1 i.2 (Sum.inl a),fun a i=> x i.1 i.2 (Sum.inr a))
  invFun x:=fun i e a=> Sum.elim (x.1.col ⟨i,e⟩) (x.2.col ⟨i,e⟩) a
  left_inv x:=by funext i e a; cases a <;> rfl
  right_inv x:=by apply Prod.ext <;> rfl

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I T G : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}
def oneTemplateCoordinates (v : Template p I) (o : OneUnit p n N) (x : Inputs p n I) :
    KeyCoordinates (KeySlots p v.t) N:=
  (rackCoordinates (KeySlots p v.t) N).symm (oneScatter v.t N (oneVolleyKeys (v.draw x) v.t o))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open LinearMap Module Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B R V : Type} [AddCommGroup B] [Module F B]
  [AddCommGroup R] [Module F R] [FiniteDimensional F R]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
def quadraticPolarRead (q : QuadraticForm F V) (P : R→ₗ[F]V) :
    V→ₗ[F]Module.Dual F R:=P.dualMap.comp q.polarBilin

variable [Fintype V] [Fintype (B→ₗ[F]V)] [Fintype (Module.Dual F R)]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev OneChannels (p : Shape) (N : ℕ) := Vec (HyperbolicIdx p.h)→ₗ[F]Vec (HyperbolicIdx N)

def oneChannelIn (p : Shape) (n : ℕ) : Vec (HyperbolicIdx p.h)→ₗ[F]OneFull p n:=
  (LinearMap.inr F _ _).comp (hyperbolicCoordinates p.h).toLinearMap

variable {p : Shape} {n N : ℕ}
def oneChannels (x : OneFrame p n N) : OneChannels p N:=x.comp (oneChannelIn p n)

def oneChannelPrice (p : Shape) := bp ((2*(p.h:ℝ))^2+2)

def oneCubePrice (p : Shape) := (oneChannelPrice p)^(Fintype.card (Comp p.g))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
def oneDualCoordinates (N : ℕ) : Vec (HyperbolicIdx N)≃ₗ[F]Vec (Fin (2* N)) :=
  (LinearEquiv.funCongrLeft F F (Equiv.sumComm (Fin N) (Fin N))).trans
    (oneAmbientCoordinates N)

def splitChannelMatrix {A J : Type} [Fintype A] [Fintype J] :
    Mat A (J⊕J)≃ₗ[F](Mat A J×Mat A J) where
  toFun M:=(fun a j=> M a (Sum.inl j),fun a j=> M a (Sum.inr j))
  invFun M:=Matrix.fromCols M.1 M.2
  left_inv M:=by ext a j; cases j <;> rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

/-- Polar channel evaluations are a bijective change of coordinates on
the entire channel pair, so their uniform law is exactly the old free law. -/
def oneChannelPairEquiv (p : Shape) (N : ℕ) : OneChannels p N≃ₗ[F]HFrame p (2* N) :=
  (((LinearEquiv.arrowCongr (LinearEquiv.refl F (Vec (HyperbolicIdx p.h)))
    (oneDualCoordinates N)).trans LinearMap.toMatrix').trans splitChannelMatrix).trans
      (LinearEquiv.prodComm F _ _)

def onePhaseCube {p : Shape} {n N : ℕ} (o : OneOrient p n N) : HCube p (2* N) :=
  fun e=> oneChannelPairEquiv p N (oneChannels (o e))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneListens (x : OneUnit p n N) : PhasePair p (2* N):=
  (onePhaseCube (x true),onePhaseCube (x false))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneFreeColumns (p : Shape) (n : ℕ) (s : Label p.b) :
    Vec (Fin n)→ₗ[F]OneFull p n:=
  quadraticPrimalIn.comp (blockRay p n s Block.Z).mulVecLin

def oneMixedRow (J : Vec (Fin n)→ₗ[F]OneFull p n) (o : OneOrient p n N) :
    (Comp p.g→ Vec (HyperbolicIdx N))→ₗ[F]Module.Dual F (Vec (Fin n)):=
  ∑ e,(quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' ((o e).comp J)).comp
    (LinearMap.proj e)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open LinearMap Module Function Finset Submodule
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
abbrev OneJointKey (p : Shape) (N : ℕ):=Comp p.g→ Vec (HyperbolicIdx N)

abbrev OneAtomKey (l : Tag p.g) (N : ℕ):=TagStar l→ Vec (HyperbolicIdx N)

abbrev OneAugur (p : Shape) (N : ℕ):=∀ l : Tag p.g,F→ OneAtomKey l N→ F

def OneLinearAugur (g : OneAugur p N) (R : ℕ):=∀ l,HasLinearCells (g l) R

def oneStarKey (l : Tag p.g) : OneJointKey p N→ₗ[F]OneAtomKey l N:=
  LinearMap.pi (fun e=> LinearMap.proj e.val)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Function LinearMap Submodule Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def onePrimalKey (o : OneOrient p n N) : Ray p n→ₗ[F]OneJointKey p N:=
  LinearMap.pi (fun e=> onePrimal (o e))

def oneAtomKeyValue (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b)
    (z : Base p.g n) : OneAtomKey l N:=oneStarKey l (onePrimalKey o (point p s z))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}
def oneCallOne (v : Template p I) (i : I) (x : Knobs p.g n) (o : OneOrient p n N):=
  oneAtomKeyValue o (v.t i) (v.s i) (lit (v.f i) (v.t i) x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
/-- A coordinate equivalence, not a pair of independently sampled frames. -/
def oneAtomSplit (l : Tag p.g) (N : ℕ) : OneAtomKey l N≃AtomKey l N where
  toFun x e b a:=x e (if b then Sum.inl a else Sum.inr a)
  invFun x e:=Sum.elim (x e true) (x e false)
  left_inv x:=by funext e a; cases a <;> rfl
  right_inv x:=by funext e b a; cases b <;> rfl

def oneLawOmega (p : Shape) (N : ℕ) (l : Tag p.g) (q : F) : Wgt (OneAtomKey l N):=
  mapW (lawOmega p N l q) (oneAtomSplit l N).symm

def oneDesc (v : Template.Solo p) (x : Knobs p.g n) (o : OneOrient p n N):=
  oneCallOne v () x o

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
def channelQuadraticMatrix {D : Type} [Fintype D] [DecidableEq D] (h : ℕ) (g : Vec D→ₗ[F]Hyperbolic h) : Mat D D:=
  Classical.choose (hyperbolic_matrix_representative h g)

variable {p : Shape} {n : ℕ} {I : Bool→ Type}
  [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
def oneAmbientPolar (N : ℕ) : LinearMap.BilinForm F (Vec (Fin (2* N))) :=
  (hyperbolicMatrix N).toQuadraticForm'.polarBilin.compl₁₂
    (oneAmbientCoordinates N).symm.toLinearMap (oneAmbientCoordinates N).symm.toLinearMap

variable {p : Shape} {n N : ℕ}
abbrev OneCross (p : Shape) (n : ℕ) := ImageCross (Comp p.g) (OneColumn p n)

def oneTableOfCross (Q : OneCross p n) (e : Comp p.g) :
    LinearMap.BilinForm F (OneUnitFull p n):=
  (Q e).toBilin'.compl₁₂ (oneNominalCoordinates p n).symm.toLinearMap
    (oneNominalCoordinates p n).symm.toLinearMap

variable {V : Type} [AddCommGroup V] [Module F V] [Fintype V]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
def unitLeftChannels (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) (j : Bool) :
    A→ₗ[F]Hyperbolic h :=
  (LinearMap.BilinForm.toDual (hyperbolicQuadratic h).polarBilin
    (hyperbolic_nondegenerate h)).symm.toLinearMap.comp
    (T.compl₁₂ (LinearMap.inl F _ _)
      ((LinearMap.inr F _ _).comp (LinearMap.single F (fun _ : Bool=> Hyperbolic h) j)))

def unitRightChannels (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) (i : Bool) :
    B→ₗ[F]Hyperbolic h := unitLeftChannels h T.flip i

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev OneCheckSide (p : Shape) (n : ℕ) :=
  Bool→ Comp p.g→ JointRay p n→ₗ[F]Hyperbolic p.h

abbrev OneCheckGram (p : Shape) (n : ℕ) := OneCheckSide p n×OneCheckSide p n

variable {p : Shape} {n N : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def onePrimalPins (P : ImagePlan (Comp p.g) (OneColumn p n)) (e : Comp p.g) : Space (JointRay p n):=
  (P e).map ((LinearMap.fst F _ _).comp (oneNominalCoordinates p n).toLinearMap)

def oneChannelPins (P : ImagePlan (Comp p.g) (OneColumn p n)) (i : Bool) (e : Comp p.g) :
    Space (Hyperbolic p.h):=
  (P e).map ((LinearMap.proj i).comp ((LinearMap.snd F _ _).comp (oneNominalCoordinates p n).toLinearMap))

variable {I : Type} [Fintype I]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def onePinSafe (P : Bool→ Comp p.g→ Space (Ray p n))
    (C : Bool→ Comp p.g→ Space (Hyperbolic p.h)) (x y : OneUnit p n N) : Prop :=
  ∀ e i j,∀ v∈P i e,
    unitLeftChannels p.h (oneUnitActual x y e) j (jointInjection i v)∈C j e→ v=0

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
def oneSelectedPrimal (v : Volley p n I) (t : Tagging p I)
    (P : Bool→ Comp p.g→ Space (Ray p n)) (e : Comp p.g) : Space (JointRay p n) :=
  jointSpace (fun i=> P i e⊔selectedAtComponent
    (fun a : CallsAt v i=> t a.val) (fun a=> v.sel a.val) (fun a=> v.par a.val) e)

/-- The protected-subspace conditions needed by the joint quadratic
annihilator, stated directly on the query's actual selected points. -/
structure OneProtectedVolley (v : Volley p n I) (t : Tagging p I)
    (P : Bool→ Comp p.g→ Space (Ray p n)) (R : ℕ) where
  selector : Bool→ Space (Vec (SelIdx p.b p.j))
  base : Bool→ Space (Vec (AIdx p.g n))
  pinCross : ∀ i e,P i e≤ tensorCross (selector i) (base i)
  selectorIndependent : ∀ i,LinearIndependent F ((selector i).mkQ∘
    fun a : CallsAt v i=> selV p.j (v.sel a.val))
  baseIndependent : ∀ i,LinearIndependent F ((base i).mkQ∘
    fun a : CallsAt v i=> baseV (v.par a.val))
  rankBound : ∀ e,2* dim (oneSelectedPrimal v t P e)≤ R
  lowPin : ∀ i e,∀ u∈P i e,Matrix.rank (flattenMatrix.symm u)≤ R^2+Fintype.card (CallsAt v i)→
    u∈tensorRectangle (selector i) (base i)

variable {N : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}
def oneEndpointPrimalPins (P : ImagePlan (Comp p.g) (OneColumn p n))
    (i : Bool) (e : Comp p.g) : Space (Ray p n) :=
  (onePrimalPins P e).map (jointProjection i)

variable {I : Type} [Fintype I] [DecidableEq I]
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneEffectivePins (P : Bool→ Comp p.g→ Space (Ray p n)) (i : Bool) : Space (Profile p n) :=
  Xspace p n⊓Submodule.pi Set.univ (fun e=> quadraticSquares (P i e))

def oneInner (x : OneUnit p n N) (i : Bool) : Profile p n→ₗ[F]F:=
  (oneFunctional (x (!i))).comp (oneMomentEmbed (x i))

variable {I : Type} [Fintype I]
structure OneScalarRecipe (v : Volley p n I) (w : I→ Bool) (t : Tagging p I)
    (m : Mixer p n) (x y : OneUnit p n N)
    (P : Bool→ Comp p.g→ Space (Ray p n)) : Prop where
  summ (i j : Bool) : ∑ a∈v.shoots w i j,v.diagonalAt a=1
  gradient (i j : Bool) (z : Profile p n) : z∈oneEffectivePins P i→
    grad m (v.sumAt t w i j) z=oneFunctional (y j) (oneMomentEmbed (x i) z)

def oneAttackGrad (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (y : OneUnit p n N) : Prop :=∀ a j,
  grad m (v.sumAt t w.obj (v.obj a) j) (v.atomAt t a)=
    if j=w.obj a then 0 else oneInner y (w.obj a) (w.atomAt t a)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
noncomputable section
variable {p : Shape} {n N : ℕ}
def oneMismatch (g : OneAugur p N) (w : Pdual p n) (l : Tag p.g)
    (s : Label p.b) (f : Flavor p.g) (o : OneOrient p n N) (y : Knobs p.g n):=
  w (useAtom p l s f y)≠g l (dialed p l f y) (oneAtomKeyValue o l s (lit f l y))

def onePostulates (o : OneOrient p n N) (g : OneAugur p N) (w : Pdual p n)
    (E : Finset (Label p.b)) (δ : ℝ):=
  ∀ s,s∉E→∀ l f,pr (spins p n) (oneMismatch g w l s f o)≤δ

def oneYoke (m : Mixer p n) (x : OneUnit p n N) (i : Bool) (u : Profile p n) (α : F):=
  oneInner x i+(Tsym m u+α • role p n)

def oneClaimed (x : OneUnit p n N) (g : Bool→ OneAugur p N) (m : Mixer p n)
    (w : Bool→ Profile p n) (α : Bool→ F) (L : Bool→ Finset (Label p.b)) (δ : ℝ):=
  ∀ i,onePostulates (x i) (g i) (oneYoke m x i (w i) (α i)) (L i) δ

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter Finset PredictionClass
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N M : ℕ}
def oneAssembly (g : Bool→ OneAugur p N) (i j : Bool) (s t : F) : OneAugur p N:=
  fun l q x=> s* g i l q x+t* g j l q x

abbrev OneSeason (p : Shape) (M : ℕ):=∀ n,OneAugur p (M* n)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PredictionClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {N : ℕ}
/-- Both predictor values are functions of fixed linear rows. The same
function is used on the two diagonal slices. -/
structure OneAlgebraicRows (g : Bool → OneAugur p N) (R : ℕ) : Prop where
  rows : ∀ i, OneLinearAugur (g i) R
  sameSlice : ∀ i l q x, g i l q x = g i l 0 x

def oneLiteral (g : OneAugur p N) (r : F) :=
  ∀ l q x,g l q x=r* q

def oneInactive (g : Bool→ OneAugur p N) (α : Party) (i : Bool) :=
  firstBit α i=0 ∧ ∃ r,oneLiteral (g i) r

def oneCoincident (g : Bool→ OneAugur p N) (α : Party) :=
  α true=α false ∧ ∃ r,oneLiteral (oneAssembly g true false 1 1) r

def oneFiniteClass (g : Bool→ OneAugur p N) (α : Party) : PredictionClass := by
  classical
  exact if oneInactive g α true then
    if oneInactive g α false then dusk else dawn false
  else if oneInactive g α false then dawn true
  else if oneCoincident g α then twinned else noon

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneDuality (N : ℕ) : Vec (Fin (2* N))≃ₗ[F]Vec (Fin (2* N)):=
  (oneAmbientCoordinates N).symm.trans (oneDualCoordinates N)

def oneDualImages (x : OneUnit p n N) (e : Comp p.g) : Mat (Fin (2* N)) (OneColumn p n):=
  LinearMap.toMatrix' (oneDuality N).toLinearMap* oneCoordinateImages x e

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev SymCover (p : Shape) (N : ℕ) := Comp p.g→ Space (Vec (Fin N))

abbrev SymWidths (p : Shape) (r : ℕ) := Comp p.g→ Fin (r+1)

abbrev SymOffsetBasis (p : Shape) (r : ℕ) {N : ℕ} (S : SymCover p N) (q : SymWidths p r) :=
  ∀ e,Mat (Fin (dim (S e))) (Fin (q e).val)

abbrev SymOffsetCost (p : Shape) (r : ℕ) (q : SymWidths p r) :=
  ∀ e : Comp p.g,Mat (Fin (q e).val) (Fin (q e).val)

abbrev SymAtlas (p : Shape) (r : ℕ) {N : ℕ} (S : SymCover p N) :=
  Σ q : SymWidths p r,SymOffsetBasis p r S q×SymOffsetCost p r q

instance symAtlasFintype {p : Shape} {r N : ℕ} (S : SymCover p N) : Fintype (SymAtlas p r S) := by
  classical
  exact inferInstanceAs (Fintype (Σ q : SymWidths p r,SymOffsetBasis p r S q×SymOffsetCost p r q))

variable {p : Shape} {r N : ℕ} {S : SymCover p N}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def onePrimalMatrix (P : OneFrame p n N) : Mat (Fin (2* N)) (Row p n):=
  LinearMap.toMatrix' ((oneAmbientCoordinates N).toLinearMap.comp (onePrimal P))

def oneHeatRate (p : Shape) (n N : ℕ) (ζ : ℝ) (q t : ℕ) :=
  bp (num (Row p n)* q+4* p.h* t)* fee (2* N) ζ (q+t)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
abbrev OneCover (p : Shape) (N : ℕ) := Comp p.g→ Space (Vec (Fin (2* N)))

def oneCoverDimension (C : OneCover p N) : ℕ:=∑ e,dim (C e)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [Fintype A] {p : Shape} {N : ℕ}
def channelPitch (Δ : A→ Ambient p N) (read : A→ PhasePair p N)
    (w : Wgt A) (S R : Party) :=
  avg (pairW w w) (fun x=> wsign
    (joinPhase p (read x.1) R (Δ x.2)+joinPhase p (read x.2) S (Δ x.1)))

variable {n : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {T : SymCover p (2* N)}
namespace OneBazaar
end OneBazaar
def oneSelectionPrice (p : Shape) (r n N : ℕ) (H ζ : ℝ) : Prop:=
  ∀ q t : ℕ,q≤ r→ t≤ r→ H* oneHeatRate p n N ζ q t≤ loseA p (2* N) q t

namespace OneBazaar
end OneBazaar
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}
def oneImageProfile (o : OneOrient p n N) : Profile p n→ₗ[F]Ambient p (2* N) where
  toFun z e:=liftM (onePrimalMatrix (o e)) (onePrimalMatrix (o e)) (z e)
  map_add' z w:=by ext e a b; simp only [Pi.add_apply,map_add,Matrix.add_apply]
  map_smul' c z:=by ext e a b; simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Matrix.smul_apply]

def oneMarkedDelta (x : OneUnit p n N) (marks : Bool→ Profile p n) : Ambient p (2* N):=
  oneImageProfile (x true) (marks true)+oneImageProfile (x false) (marks false)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneBySide (w : Wgt (OneUnit p n N)) (m : Mixer p n) (H : ℝ) : Prop :=
  ∀ i o,mapW w (fun x=> x i) o≤ H* oneRaw m N o

abbrev OnePrimalPinFamily (p : Shape) (n N : ℕ) :=
  OneUnit p n N→ Bool→ Comp p.g→ Space (Ray p n)

abbrev OneChannelPinFamily (p : Shape) (n N : ℕ) :=
  OneUnit p n N→ Bool→ Comp p.g→ Space (Hyperbolic p.h)

def oneAcceptsPin (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (x : OneUnit p n N×OneUnit p n N) :=onePinSafe (P x.1) (B x.2) x.1 x.2

def oneSecurePin (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (x : OneUnit p n N×OneUnit p n N) :=oneAcceptsPin P B x ∧ oneAcceptsPin P B x.swap

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
abbrev OneLeafMixture (p : Shape) (n N : ℕ):=
  ImageLeafMixture (OneUnit p n N) (Comp p.g) (OneColumn p n) (2* N)

def oneLeafStrength (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N))
    (m : Mixer p n) (D ζ : ℝ) (K : ℕ):=
  s.strength oneCoordinateImages (onePinClosure p n) w (oneUnitRaw m N) D ζ K

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
def oneGradientRank (p : Shape) : ℕ :=
  2*(15* p.r+14* p.J* Fintype.card (Comp p.g))

def oneRealizationRoom (p : Shape) (K t : ℕ) : Prop :=
  let f:=2*(K+t)
  oneGradientRank p+(f+K)+jointCompressionRank p f (2* f+(f+K))+5* K+6* f+2≤ p.h

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {T : SymCover p (2* N)}
def oneGlimpseBill (p : Shape) (r : ℕ) (H : ℝ):=num (Comp p.g)*(H*2* bp ((r:ℝ)-p.h))

namespace OneBazaar
end OneBazaar
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {T : SymCover p (2* N)}
def oneQuest (p : Shape) (r k n N : ℕ) (H ε : ℝ) :=
  ∀ x : ℕ,x≤ r →
    bp ((x:ℝ)*(2* N))* bp (0.51* k*(2* N))*(H* oneHeatRate p n N ε x k)≤ bp (-0.2*(2* N))

namespace OneBazaar
end OneBazaar
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}
def oneSymCov {p : Shape} {N : ℕ} (C : SymCover p N) : Cov p N:=fun z=> C z.1

def oneSymCovered {p : Shape} {N : ℕ} (C : SymCover p N) (x : Ambient p N):=covered p (oneSymCov C) x

def oneTonalMix {p : Shape} {n N} (Δ : OneUnit p n N → Ambient p (2* N)) (w) :=
  ∀ S R,S ≠ 0 ∨ R ≠ 0 → |channelPitch Δ oneListens w S R|< 0.005

def oneTonalTiny {p : Shape} {n N} (Δ : OneUnit p n N → Ambient p (2* N)) (w : Wgt (OneUnit p n N)) (d : ℕ) :=
  ∃ S : SymCover p (2* N), oneCoverDimension S≤ d ∧ (∀ x,w x≠0 → oneSymCovered S (Δ x)) ∧
    ∀ i : Bool,∀ R : Party, |channelPitch Δ oneListens w (unary i) R|≤ bp (-0.24*(2* N))

namespace OneBazaar
variable {T : SymCover p (2* N)}
end OneBazaar
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneQuench (Δ : OneUnit p n N→ Ambient p (2* N))
    (x : OneUnit p n N×OneUnit p n N) : Quad :=
  (fun i=> joinPhase p (oneListens x.2) (unary i) (Δ x.1),
   fun i=> joinPhase p (oneListens x.1) (unary i) (Δ x.2))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Function Finset PredictionClass
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneMatchUp (Δ : OneUnit p n N→ Ambient p (2* N)) (α : Party) (r : F)
    (c : PredictionClass) (x : OneUnit p n N×OneUnit p n N) :=
  c.compatible α r (oneQuench Δ x)

def oneExactInk (m : Mixer p n) (marks : OneUnit p n N→ Bool→ Profile p n)
    (x : OneUnit p n N) := ∀ i,silent (oneYoke m x i (marks x i) 1)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Function Finset PredictionClass
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
/-- A finite label for each unit determines a relation on pairs. The bound
counts labels in either coordinate, including after transposing the test. -/
structure PairCode (A : Type) (budget : ℝ) where
  count : ℕ
  fits : (count:ℝ)≤ budget
  label : A→ Fin count
  test : Fin count × Fin count → Prop

def PairCode.read {A : Type} {B : ℝ} (c : PairCode A B) (v : A×A) :=
  c.test (c.label v.1,c.label v.2)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}
def oneScaleBill (p : Shape) (n N d : ℕ) (H : ℝ):=
  2* num (Comp p.g)* H* bp (num (Row p n)+d+3-2*(N:ℝ))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}
def oneNoSweepBudget (p : Shape) (N m b r : ℕ) (c ψ H : ℝ):=
  bp (2*(r:ℝ)* num (Comp p.g)*(2* N))*(H* oneCubePrice p^2*
    (exponentErr p m b c/ψ^(2^m*(2* b))))

/-- All numerical costs of the one-frame phase argument. The raw image
cap is the concrete quadratic-frame cap, not a two-frame assumption. -/
structure OnePhaseReady (p : Shape) (n N m b r k d : ℕ) (mix : Mixer p n)
    (c l ψ ε L H : ℝ) : Prop where
  hb : 1≤ b
  hm : 16* r< m
  hk : k≤ d
  hc : 0< c
  hc' : c≤1
  hl : 0< l
  hl' : l≤1
  hψ : 0<ψ
  hL : 0≤ L
  hH : 0≤ H
  hroom : Fintype.card (Row p n)+2* p.h+1≤ N
  hN : 5≤ N
  hchannels : 4* p.h+3≤ N
  cap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2* N),
    pr (oneUnitRaw mix N) (imagePinAgree oneDualImages a)≤ fee (2* N) ε (imagePlanRank a.sp)
  noBranch : ψ+oneNoSweepBudget p N m b r c ψ H<0.005
  frames : oneScaleBill p n N (2* maxSpan m b r) L≤ c/2
  atlas (T : SymCover p (2* N)) (ht : oneCoverDimension T≤2* maxSpan m b r) :
    num (SymAtlas p r T)≤ bp (0.002*(2* N))
  price : oneSelectionPrice p r n N (rhUp L c) ε
  price' : oneSelectionPrice p r n N (rhUp (rhUp L c) l) ε
  localQ : oneQuest p r k n N (rhUp H c) ε
  testFailure : oneGlimpseBill p k (rhUp L c)+bp (-0.1*(2* N))< l^(k+1)
  testFailure' : 2* oneGlimpseBill p d (rhUp L c)≤ l/2
  beatSlack : 5* l+bp (-0.24*(2* N))<0.005

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ}
abbrev OneTale (p : Shape) (M : ℕ):=∀ n,Wgt (OneUnit p n (M* n))

abbrev OneRhythms (p : Shape) (M : ℕ):=∀ n,OneLeafMixture p n (M* n)

abbrev OneMarks (p : Shape) (n N : ℕ):=OneUnit p n N→ Bool→ Profile p n

def oneFrameSide (m : Mixer p n) (x : OneUnit p n N):=∀ i,oneFrameLaw m (x i)

def onePreparationPins (q : PreparationParameters):=q.e+q.s

/-- A symmetric cover of dimension d gives a two-sided cover of dimension 2d. -/
def onePreparationCover (q : PreparationParameters):=2* q.d

structure OnePreparationAllows (q : PreparationParameters) : Prop where
  pos : 0< q.ζ
  small : q.ζ<1
  hL : 0≤ q.L
  bigS : q.leafOld+q.u+q.ζ≤((q.ζ/6)-(q.ζ/6)/4)* q.s

structure OneNascent (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) : Prop where
  law : IsLaw w
  border : oneBySide w m q.L
  total : ∀ x,w x≤ bp ((q.D:ℝ)*(2* N))* oneUnitRaw m N x

structure OneEntered (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) (s : OneLeafMixture p n N) : Prop where
  weight : (1/2:ℝ)≤ s.amount w
  strength : oneLeafStrength s w m q.leafOld q.ζ q.e
  onTile : s.within (fun x=> w x≠0 ∧ (oneRawHoles m).unit (x true,x false) ∧
    oneFrameSide m x)

structure OneDurable (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (s : OneRhythms p M) : Prop where
  mass : warm l (fun n=>(2*(M* n):ℕ)) (fun n=>(s n).amount (w n))
  shape : ∀ᶠ n in l,oneLeafStrength (s n) (w n) (m n) q.leafNew (2* q.ζ)
    (onePreparationPins q) ∧ (s n).within (oneFrameSide (m n))
  retained : ∃ c : ℝ,0< c ∧ ∀ᶠ n in l,c≤(s n).amount (w n)

def oneSeems (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (x : OneUnit p n N) (g : Bool→ OneAugur p N) (z : Bool→ Profile p n)
    (L : Bool→ Finset (Label p.b)) (α : Party) (ε : ℝ):=
  (∀ i,(L i).card≤ q.B ∧ z i∈oneEffectivePins (oneEndpointPrimalPins (s.rooting x)) i) ∧
    oneClaimed x g m z α L ε

def oneSecureAt (s : OneLeafMixture p n N):=
  oneSecurePin (fun x=> oneEndpointPrimalPins (s.rooting x))
    (fun x=> oneChannelPins (s.rooting x))

structure OneSketch (p : Shape) (M : ℕ) where
  c : PredictionClass
  α : Party
  r : F
  m : ∀ n,OneMarks p n (M* n)
  L : ∀ n,OneUnit p n (M* n)→ Bool→ Finset (Label p.b)
  g : Bool→ OneSeason p M
  ε : ℕ→ ℝ

def oneMatchProg (b : OneSketch p M) (n : ℕ):=
  oneMatchUp (fun x=> oneMarkedDelta x (b.m n x)) b.α b.r b.c

def oneGlow (s : OneRhythms p M) (w : OneTale p M) (b : OneSketch p M) (n : ℕ):=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (oneMatchProg b n)

def oneGleam (s : OneRhythms p M) (w : OneTale p M) (b : OneSketch p M) (n : ℕ):=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
    (fun x=> oneMatchProg b n x ∧ ¬oneSecureAt (s n) x)

abbrev OneCompatibilityCode (q : PreparationParameters) (p : Shape) (n N : ℕ) :=
  PairCode (OneUnit p n N) (bp (3*(onePreparationCover q)*(2* N:ℝ)))

def oneCodedLeaves (q : PreparationParameters) (s : OneLeafMixture p n N)
    (R : OneUnit p n N × OneUnit p n N → Prop) :=
  ∃ code : OneCompatibilityCode q p n N,
    (∀ i∈s.T,∀ x∈i,∀ y∈i,code.label x=code.label y) ∧
    ∀ x y,inTiles s.T x → inTiles s.T y → (code.read (x,y) ↔ R (x,y))

def oneOutside (q : PreparationParameters) (p : Shape) (n N : ℕ):=
  ∀ E : OneUnit p n N×OneUnit p n N→ Prop,named E (bp (3*(onePreparationCover q)*(2* N:ℝ)))→
    named (E∘Prod.swap) (bp (3*(onePreparationCover q)*(2* N:ℝ)))→
    ∀ w (s : OneLeafMixture p n N) (m : Mixer p n),
      (∀ x,imagePlanRank (s.rooting x)≤ onePreparationPins q)→
      IsLaw w→ oneBySide w m (shine (2* N))→ carried w (oneFrameSide m)→
      pr (pairW w w) (fun x=> E x ∧ ¬oneSecureAt s x)≤
        0.0005* pr (pairW w w) E+edgeError (2* N)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K:ℕ} {C ζ:ℝ}
abbrev OneAspect (pop:OneLeafMixture p n N):=pop.T×OneUnit p n N

def oneTroupe (pop:OneLeafMixture p n N) (μ:Wgt (OneUnit p n N)):=
  semi (portionW μ pop.T) (fun i=> partW μ i.val)

def oneCirque (pop:OneLeafMixture p n N) (μ:Wgt (OneUnit p n N)):=
  pairW (oneTroupe pop μ) (oneTroupe pop μ)

structure OneLead (μ:Wgt (OneUnit p n N)) (pop:OneLeafMixture p n N)
    (m:Mixer p n) (C ζ:ℝ) (K:ℕ):Prop where
  strength:oneLeafStrength pop μ m C ζ K
  amount:0< pop.amount μ
  law:IsLaw μ
  cover:pop.within (oneFrameSide m)

variable {pop:OneLeafMixture p n N} {μ:Wgt (OneUnit p n N)} {m:Mixer p n}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Module Submodule Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {d : Rates}
def oneCharted (v : Charts p n d) (a : ImagePlan (Comp p.g) (OneColumn p n)) :=
  ∀ i,LinearMap.range (v i)=oneEffectivePins (oneEndpointPrimalPins a) i ∧ Injective (v i)

def oneSpecify (p : Shape) {d : ℕ} (i : Nodes) (v : Ax p n d)
    (m : Mixer p n) (o : OneUnit p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (x : Knobs p.g n) : Magazine p d :=
  let A:=useAtom p l s f x
  (scan p l f x,(role p n A,roll v (Tsym m A)),oneInner o i A)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}
abbrev OneSilhouette (p : Shape) (N r : ℕ):=∀ l : Tag p.g,F→ OneAtomKey l N→ Fin r

namespace OneAppearance
variable (x : Appearance p)
def oneFace (o : OneOrient p n N) (w : Knobs p.g n) : OneAtomKey (p:=p) x.l N :=
  oneDesc x.trot w o

def oneProfile {d : ℕ} (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d)
    (z : Knobs p.g n) : Magazine p d :=
  oneSpecify p i v m o x.l x.s x.f z

variable (Y : OneSilhouette p N r)
def oneShowTag (o : OneOrient p n N) := fun w=> Y x.l x.q (oneFace x o w)

def oneReference := mapW (oneLawOmega p N x.l x.q) (Y x.l x.q)

def oneEmpirical (o : OneOrient p n N) := mapW (x.wit n) (oneShowTag x Y o)

variable {d : ℕ}
def oneReflected (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Ax p n d) (a : Fin r) :=
  mapW (stained (x.wit n) (oneShowTag x Y (o i)) a) (oneProfile x i o m v)

def oneClose (o : OneOrient p n N) (ε : ℝ) :=
  varOne (oneReference x Y) (oneEmpirical x Y o) ≤ ε

end OneAppearance
namespace OneAppearance
variable (x : Appearance p) (Y : OneSilhouette p N r)
variable {d : ℕ}
end OneAppearance
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K s : ℕ}
variable (v : Template.Solo p)
def oneOffBeat (v : Template.Solo p) (P : OneAtomKey (p:=p) (v.t ()) N → Prop) (o : OneOrient p n N) :=
  fun z => P (oneDesc v z o)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Template Finset Matrix Function LinearMap Module Submodule Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneLuminous (v : Template.Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n)) (D : OneAtomKey (p:=p) (v.t ())
    N → Prop) (K : ℕ) (i : OneOrient p n N) :=
  let P := oneOffBeat v D i
  0< pr w P ∧ ∀ (d : ℕ), d≤ K^2 → ∀ f : Vec (Fin d)→ₗ[F] Profile p n,
    Injective f → (∀ x,totalRank (f x)≤ K) → ∀ x,
    (7/8:ℝ)* bp (-(d:ℝ)) ≤ pr (onW w P) (fun z=> stains v m f z=x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Template Finset Matrix Function LinearMap Module Submodule Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
variable (v : Solo p)
def onePatrol (m : Mixer p n) (w : Wgt (Knobs p.g n))
    (S : OneAtomKey (p:=p) (v.t ()) N→ Prop) (K : ℕ) (q : F) (x : OneOrient p n N) :=
  oneLuminous v m w S K x ∧
    3/4* pr (oneLawOmega p N (v.t ()) q) S ≤ pr w (oneOffBeat v S x)

variable {K s : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function Template
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K M r : ℕ}
structure OneUnaryParameters (p : Shape) (M K s : ℕ) : Prop where
  hM : 1≤ M
  hg : Odd p.g
  hJ : 1≤ p.j
  hR : 1≤ p.r
  profiles : 2* profileA p K< s
  gleaming : bp (-((p.J-s:ℕ):ℝ))* bp s< glintRate K

namespace OneAppearance
variable (x : Appearance p) {s0 : ℕ}
def oneFoil (x : Appearance p) (Y : OneSilhouette p N r) (o : OneOrient p n N)
    (m : Mixer p n) (K : ℕ) (δ : ℝ) :=
    ∀ (z:Digest p.g) (i:Fin r), z.feasible x.l x.f → z.sumBit=x.q →
      δ ≤ oneReference x Y i → onePatrol x.trot m (scopedScan p n x.l x.f z)
        (fun y => Y x.l x.q y=i) K x.q o

end OneAppearance
open OneAppearance
variable {s0 : ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Template StatusAnalysis StatusAnalysis.DualAnalysis OneAppearance Filter Finset Matrix Function LinearMap Module
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {d : Rates}
def oneWisp (p : Shape) (Y : OneSilhouette p N r) : Terrain p r:=
  fun l q=> mapW (oneLawOmega p N l q) (Y l q)

def oneWake (p : Shape) (Y : OneSilhouette p N r) (m : Mixer p n) (o : OneUnit p n N)
    (s : Charts p n d) : Gazette p r d:=fun i x a=> oneReflected x Y i o m (s i) a

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis OneAppearance Template
open Matrix Filter Finset LinearMap Module Function
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r n N : ℕ} {d : Rates}
def oneFromPulse (Y: OneSilhouette p N r) (f:Pulsar p r) : OneAugur p N :=
  fun l q x=> f l q (Y l q x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {T : Type} {p : Shape} {N r s K R : ℕ}
def OneLinearSilhouette (Y : OneSilhouette p N r) (K : ℕ) :=
  ∀ l,HasLinearCells (Y l) K

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}
def oneQueryCoordinateEquiv (t : Tagging p I) (N : ℕ) :
    KeyCoordinates (KeySlots p t) N ≃ OneKeys t N :=
  (rackCoordinates (KeySlots p t) N).toEquiv.trans (oneScatter t N).symm

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  {p : Shape} {n N : ℕ}
/-- The one-frame reference fixes quadratic values and polar pairings
within each component, without fixing ordered products of its halves. -/
def oneOwnPart (t : Tagging p I) (q : I → F)
    (x : KeyCoordinates (KeySlots p t) N) : Prop:=
  quadraticTraced (crowded (ownPort t)) (geoMatrix (ownPort t) (ownMap t q)) x

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {p : Shape} {N : ℕ}
def oneOwnKeyPart (t : Tagging p I) (q : I→ F) (x : OneKeys t N):=
  oneOwnPart t q ((oneQueryCoordinateEquiv t N).symm x)

def oneLawNu (p : Shape) (N : ℕ) (t : Tagging p I) (q : I→ F) : Wgt (OneKeys t N):=
  unifOn (oneOwnKeyPart t q)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N R r s : ℕ} {I T : Type} [Fintype I] [DecidableEq I]
def OneRefines (Y : OneSilhouette p N r) (X : OneSilhouette p N s):=
  ∀ l q,∃ f : Fin r→ Fin s,∀ x,X l q x=f (Y l q x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Module Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N r s K R : ℕ} {I T : Type} [Fintype I] [DecidableEq I]
def OneFullLinearSilhouette (Y : OneSilhouette p N r) (K : ℕ) :=
  ∀ l,HasFullLinearCells (Y l) K

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
variable {g : ℕ}
/-- The vertex at the start of an oriented cycle component. -/
def cycleOrigin (e : Comp g) : Tag g :=
  if h : 3≤ g then (CycleGeometry.forwardEquiv h).symm e else e.val.1

def cycleWeight (e f : Comp g) : F :=
  if h : 2≤ g then ∑ i : Fin ((g-1)/2),
    if CycleGeometry.forward h (CycleGeometry.matchingVertex (cycleOrigin e) i)=f then 1 else 0
  else 0

theorem matching_vertex_injective (t : Tag g) :
    Injective (CycleGeometry.matchingVertex t) := by
  intro i j h
  have he:=congrArg Fin.val (add_right_cancel h)
  apply Fin.ext
  dsimp only [CycleGeometry.matchingVertex] at he
  omega

theorem cycle_weight_exists (hg : 3≤ g) (e : Comp g) : ∃ f,cycleWeight e f=1 := by
  let i : Fin ((g-1)/2):=⟨0,by omega⟩
  let f:=CycleGeometry.forward (by omega : 2≤ g) (CycleGeometry.matchingVertex (cycleOrigin e) i)
  refine ⟨f,?_⟩
  simp only [cycleWeight,dif_pos (show 2≤ g by omega)]
  rw [sum_eq_single i]
  · simp [f]
  · intro j _ hji
    rw [if_neg]
    intro h
    exact hji (matching_vertex_injective _ (CycleGeometry.forward_injective hg h))
  simp

/-- One representative suffices to store the matrix for a whole matching. -/
def cycleAnchor (e : Comp g) : Comp g :=
  if hg : 3≤ g then (cycle_weight_exists hg e).choose else e

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}
abbrev ReducedIndex (p : Shape):=Fin p.J × Comp p.g

abbrev ReducedOne (p : Shape):=ReducedIndex p × Bool

abbrev ReducedBits (p : Shape):=ReducedOne p × Bool

def reducedSlot (i : ReducedOne p) : MOne p:=
  ((i.1.1,i.1.2,cycleAnchor i.1.2),i.2)

def reducedOrdered (m : Mixer p n) (i : ReducedOne p):=orderedM m (reducedSlot i)

def reducedIndexedSum (m : Mixer p n) (c : Vec (ReducedBits p)):=
  ∑ i,c i •eitherM i.2 (reducedOrdered m i.1)

/-- The expanded storage table contains only one independent L/R pair per
cycle component. It is retained as an adapter to the scalar geometry API. -/
def ReducedMixerLaw (m : Mixer p n) : Prop :=
  3≤ p.g ∧
    (∀ j e f,m.mixL j e f=cycleWeight e f •m.mixL j e (cycleAnchor e)) ∧
    (∀ j e f,m.mixR j e f=m.mixR j e (cycleAnchor e))

def reducedBinaryGood (m : Mixer p n) : Prop :=
  ReducedMixerLaw m ∧ ∀ s t : Label p.b,s≠t→
    ∀ (c : Vec (ReducedBits p)) (b : Vec Bool),c≠0 ∨ b≠0→
      n≤5* blockRank Block.sharp s t (reducedIndexedSum m c+selfSum m b)

/-- Expand one set of independent prescribed bits along the cycle matchings. -/
def reducedScript {I : Type} (s : Script p I) : Script p I:=fun x y i=>
  if i.2 then cycleWeight i.1.2.1 i.1.2.2* s x y ((i.1.1,i.1.2.1,cycleAnchor i.1.2.1),true)
  else s x y ((i.1.1,i.1.2.1,cycleAnchor i.1.2.1),false)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Function Finset Filter
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
abbrev OneCrossing (p : Shape) (l d : Tag p.g):={e : Comp p.g//inc e l ∧inc e d}

abbrev OneHarm (p : Shape) (l d : Tag p.g):=
  ReducedBits p⊕{u : Unit//Template.sharesComponent p l d}

abbrev oneAbbey (v : Template p I) : v.Chorus→ Type
  | .inl i=> OneHarm p (v.t i.val.1) (v.t i.val.2)
  | .inr i=> OneCrossing p (v.t i.val.1) (v.t i.val.2)

instance (v : Template p I) (i : v.Chorus) : Fintype (oneAbbey v i):=
  i.rec (fun _=> inferInstanceAs (Fintype (OneHarm p _ _)))
    (fun _=> inferInstanceAs (Fintype (OneCrossing p _ _)))

instance (v : Template p I) (i : v.Chorus) : DecidableEq (oneAbbey v i):=Classical.typeDecidableEq _

def oneKappa (v : Template p I):=wavelength (oneAbbey v)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}
def oneQueryWeightBad (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (b ε : ℝ) (o : OneUnit p n N) : Prop :=
  ∃ w : Wgt (Inputs p n I),inputFourierNorm w≤ b ∧
    ε < |avg unif (fun x=> D (oneTemplateCoordinates v o x)*ψ x* w x)|

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  {p : Shape} {n N : ℕ}
def oneQueryPValues (v : Template p I) (o : OneUnit p n N) (x : Inputs p n I) : I→ F :=
  fun i=> oneInner o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i) (x i))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  {p : Shape} {n N : ℕ}
def oneQueryFlags (v : Template p I) (χ : Inputs p n I→ A)
    (o : OneUnit p n N) (x : Inputs p n I) : A×(I→ F):=(χ x,oneQueryPValues v o x)

def oneQueryReferenceSet (v : Template p I) (q : I→ F) (N : ℕ) :
    KeyCoordinates (KeySlots p v.t) N→ Prop :=
  fun x=> oneOwnPart v.t q x

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}
/-- The scalar status vocabulary is unchanged; its parity coordinate now
comes from the single quadratic frame and its opposite channels. -/
def onePrinted (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q→ Label p.b) (f : Messenger q→ Flavor p.g) (m : Mixer p n)
    (o : OneUnit p n N) (x : Inputs p n (Messenger q)) : Amounts p q d b :=
  joinPrinted (nominalPrinted b v t s f m x) (oneQueryPValues (manager b t s f) o x)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→ F)
  (o : OneUnit p n N)
variable (m : Mixer p n)
def oneSeraph (s : Charts p n d) (Y : OneSilhouette p N r) (i : Messenger q) :
    Wgt (OneAtomKey (p:=p) (t i) N):=fun h=>
  OneAppearance.oneReflected (w.allure t z i) Y (parcel b i) o m
    (s (parcel b i)) (Y (t i) (z i) h) (w.amp i)

end OneQuill
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
def supportLower (θ a : ℝ) : ℝ:=θ* ind (0< a)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis LinearMap Module Matrix Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N d : ℕ}
/-- This budget records the tester coordinates once, then two factors
for each basis quadratic and for the internal status bit. -/
def oneStatusCoordinateBound (p : Shape) (d K : ℕ) : ℕ :=
  Fintype.card (Gauge p)+d*(2*(p.J* tagDegree p.g*(2* K)))+
    2*(tagDegree p.g*(2* p.h))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace OneQuill
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→ F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)
def oneSupportSeraph (θ : ℝ) (i : Messenger q) : Wgt (OneAtomKey (p:=p) (t i) N):=
  fun x=> supportLower θ (oneSeraph w t z o m s Y i x)

end OneQuill
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates} {b : Bool}
namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→ F)
  (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→ Prop)
  (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)
end OneQuill
namespace OneTypus
variable (w : Typus p q d e) (o o' : OneUnit p n N)
  (s : Charts p n d) (t : Charts p n e) (m : Mixer p n) (Y : OneSilhouette p N r)
def oneMomus :=oneKappa (w.qA.pen w.t)* oneKappa (w.qB.pen w.t)

end OneTypus
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace OneTypus
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates}
variable (w : Typus p q d e) (o o' : OneUnit p n N)
  (s : Charts p n d) (t : Charts p n e) (m : Mixer p n) (Y : OneSilhouette p N r)
def oneSupportChimera (i : Messenger q):=
  dip (oneLawOmega p N (w.t i) (w.z i)) (OneQuill.oneSupportSeraph w.qA w.t w.z o m s Y 1 i)
    (OneQuill.oneSupportSeraph w.qB w.t w.z o' m t Y 1 i)

def oneSupportConstellation:=oneMomus w*∏ i,oneSupportChimera w o o' s t m Y i

end OneTypus
namespace OneTypus
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates}
variable (w : Typus p q d e) (μ ρ : Wgt (OneUnit p n N))
  (F G : OneUnit p n N→ Prop) (s : Charts p n d) (t : Charts p n e)
  (m : Mixer p n) (Y : OneSilhouette p N r) (θ : ℝ)
end OneTypus
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
def oneProtectionThreshold (K t : ℕ):=(4*(K+t))^2+t

def oneSelectorProtectionDim (p : Shape) (K : ℕ):=
  oneProtectionThreshold K 28*(Fintype.card (Bool×Comp p.g)* K)

def oneBaseProtectionDim (p : Shape) (K : ℕ):=
  Fintype.card (SelIdx p.b p.j)*(Fintype.card (Bool×Comp p.g)* K)

def OnePenSpace (v : Template p I) (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) : Prop :=
  (∀ e,dim (a e)≤ K) ∧
  ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
    dim U≤ oneSelectorProtectionDim p K ∧ dim V≤ oneBaseProtectionDim p K ∧
    (∀ i e,oneEndpointPrimalPins a i e≤ tensorCross U V) ∧
    (∀ i e x,x∈oneEndpointPrimalPins a i e→
      Matrix.rank (flattenMatrix.symm x)≤ oneProtectionThreshold K (Fintype.card I)→
      x∈tensorRectangle U V) ∧
    LinearIndependent F (U.mkQ ∘ (fun j=> selV p.j (v.s j)))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis
noncomputable section
variable {p : Shape} {q : Format} {d e : Rates}
/-- Scalar compatibility of the deterministic expansion of the smaller
binary prescription. All other status and flag conditions are unchanged. -/
def onePermission (w : Typus p q d e) : Prop :=
  (∀ i,1≤ q i ∧q i≤7) ∧w.qA.moral w.t w.z ∧w.qB.moral w.t w.z ∧
  (∀ i,fullq w.z i=1) ∧rhyme w.qA.amp w.qB.amp ∧
  proclaims p w.qA.amp w.qB.amp w.t (reducedScript w.qA.script) ∧
  proclaims p w.qB.amp w.qA.amp w.t (reducedScript w.qB.script)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}
def oneChannelInjection (p : Shape) (n : ℕ) : (Bool→ Hyperbolic p.h)→ₗ[F]Vec (OneColumn p n):=
  (oneNominalCoordinates p n).symm.toLinearMap.comp (LinearMap.inr F _ _)

def oneAllChannels (p : Shape) (n : ℕ):=LinearMap.range (oneChannelInjection p n)

def oneTabSpace (a : ImagePlan (Comp p.g) (OneColumn p n)) (e : Comp p.g):=
  a e⊔oneAllChannels p n

def oneFitsTable (a b : ImagePlan (Comp p.g) (OneColumn p n)) (T Q : OneCross p n) :=
  ∀ e,∀ v∈oneTabSpace a e,∀ w∈oneTabSpace b e,evmat (T e) v w=evmat (Q e) v w

def oneDeckMax (p : Shape) (K : ℕ):=Fintype.card (Comp p.g)*(K+4* p.h)^2

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Module Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneTableFlag (a b : ImagePin (Comp p.g) (OneColumn p n) (2* N))
    (T : OneCross p n) (x : OneUnit p n N) :=
  ∀ e,∀ v∈oneTabSpace a.sp e,∀ w∈b.sp e,
    evmat (T e) v w=oneAmbientPolar N (oneCoordinateImages x e*ᵥv) (b.target e*ᵥw)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Module Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ}
def oneContract (T : OneCross p n) (i j : Bool) : Profile p n→ₗ[F]F:=
  (jointMatrixFunctional (fun e=> channelQuadraticMatrix p.h
    (unitLeftChannels p.h (oneTableOfCross T e) j))).comp (jointEndpointMap i)

def oneTableSafe (a b : ImagePlan (Comp p.g) (OneColumn p n)) (T : OneCross p n) :=
  ∀ e i j,∀ v∈oneEndpointPrimalPins a i e,
    unitLeftChannels p.h (oneTableOfCross T e) j (jointInjection i v)∈oneChannelPins b j e→ v=0

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function LinearMap Module Submodule
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def oneTargetMark (v : Charts p n d) (T : OneCross p n) (i j : Bool) : Cell (d i):=
  roll (v i) (oneContract T i j+role p n)

def oneHailing (v : Charts p n d) (w : Charts p n e) (T : OneCross p n) : Cabinet d e:=
  fun i=>(1,1,oneTargetMark v T i.1 i.2,oneTargetMark w (fun e=>(T e)ᵀ) i.2 i.1)

def oneStill (b : Bool) (a : Amounts p q d b) (v : Charts p n d) (T : OneCross p n) :=
  (∀ i:Grid,(funds a i).1.2=oneTargetMark v T (sendId b i) (sendId (!b) i)) ∧
    ∀ j:Bool,couple _ (funds a (transit b (true,j)))=
      couple _ (funds a (transit b (false,j)))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneOptions
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates} {side : Bool}
def signed (w : Quill p q d side) (t : Tagging p (Messenger q))
    (x y : ImagePin (Comp p.g) (OneColumn p n) (2* N))
    (s : Charts p n d) (T : OneCross p n) (K : ℕ) :=
  oneCharted s x.sp ∧ OnePenSpace (w.pen t) x.sp K ∧
    oneStill side w.amp s T ∧ oneTableSafe x.sp y.sp T

def chances (w : Typus p q d e) (s : Charts p n d) (v : Charts p n e)
    (x y : ImagePin (Comp p.g) (OneColumn p n) (2* N)) (T : OneCross p n) (K : ℕ) :=
  (onePermission w) ∧ signed w.qA w.t x y s T K ∧
    signed w.qB w.t y x v (fun e=>(T e)ᵀ) K

def notified (m : Mixer p n) (x y : ImagePin (Comp p.g) (OneColumn p n) (2* N))
    (T : OneCross p n) (C : Prop) (o : OneUnit p n N) :=
  C ∧ imagePinAgree oneCoordinateImages x o ∧
    (∀ i,oneFrameLaw m (o i)) ∧ oneTableFlag x y T o

end OneOptions
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K : ℕ}
abbrev OneScrip (p : Shape) (K : ℕ):=Σ q : Master K,Fin (2^oneDeckMax p K)×OnFile p q

structure OneStation (p : Shape) (n N K : ℕ) (s : OneLeafMixture p n N) where
  cAxes : s.T→(d : Rates)→ Charts p n d
  mails : s.T→ s.T→ Fin (2^oneDeckMax p K)→ OneCross p n

namespace OneStation
variable {s : OneLeafMixture p n N} (v : OneStation p n N K s)
def bank :=
  (∀ i,let d:=fun j=> dim (oneEffectivePins (oneEndpointPrimalPins (s.pin i.val).sp) j)
    oneCharted (v.cAxes i d) (s.pin i.val).sp) ∧
  ∀ i j T,∃ k,oneFitsTable (s.pin i.val).sp (s.pin j.val).sp (v.mails i j k) T

variable {q:Format} {d e:Rates} (w:Typus p q d e)
def news (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneOptions.chances w (v.cAxes i d) (v.cAxes j e) (s.pin i.val) (s.pin j.val) (v.mails i j k) K

def frontPage (m:Mixer p n) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneOptions.notified m (s.pin i.val) (s.pin j.val) (v.mails i j k) (v.news w i j k)

def backPage (m:Mixer p n) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneOptions.notified m (s.pin j.val) (s.pin i.val) (fun e=>(v.mails i j k e)ᵀ) (v.news w i j k)

end OneStation
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
def oneMaxSlots (p : Shape):=28* tagDegree p.g

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates}
def oneClash (m : Mixer p n) (xy : OneUnit p n N×OneUnit p n N) :=
  (oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false)

structure OneEarnsScore (p : Shape) (n N K : ℕ) (ζ : ℝ) : Prop where
  hr : 1≤ p.r
  hn : 2* p.r≤ n
  odd : Odd p.g
  room : ∀ t≤28,oneRealizationRoom p K t
  smooth : 0≤ζ
  low : ζ≤0.004
  light : ζ* oneMaxSlots p≤0.004
  hN : 100≤2* N
  gram : (dim (OneCheckGram p n):ℝ)≤0.01*(2* N)
  budget : (K+(oneMaxSlots p:ℝ))* num (OneColumn p n)≤0.005*(2* N)

namespace OneStation
variable {pop : OneLeafMixture p n N} (v : OneStation p n N K pop)
end OneStation
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K r:ℕ} {pop:OneLeafMixture p n N}
namespace OneStation
def twilight {q:Format} {d e:Rates} (v:OneStation p n N K pop)
    (w:Typus p q d e) (m:Mixer p n) (k:Fin (2^oneDeckMax p K))
    (Y:OneSilhouette p N r) (i j:pop.T) (o:OneUnit p n N×OneUnit p n N):=
  ind (v.frontPage w m i j k o.1 ∧ v.backPage w m i j k o.2)*
    OneTypus.oneSupportConstellation w o.1 o.2 (v.cAxes i d) (v.cAxes j e) m Y

end OneStation
def oneSupportBudget (p:Shape) (K:ℕ) (η a:ℝ):=
  0< a ∧ ∀ k:OneScrip p K,a≤ OneTypus.oneMomus k.2.2*
    η^Fintype.card (Messenger (toFormat k.1.1))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis StatusAnalysis.Guild StatusAnalysis.Club
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N r K : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e} {β η δ : ℝ}
def oneScalarBudget (p : Shape) (K : ℕ) :=
  2^(oneSelectorProtectionDim p K+34)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneScreenRank (p : Shape) (K : ℕ) := (tagDegree p.g)*(2* p.h+2* p.J* K)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}
def oneIntern (q : PreparationParameters) (p : Shape) (n N : ℕ):=
  ∀ m : Mixer p n,OnePhaseReady p n N (mstep q.rank) ((2* N)/denomStep q.rank)
    q.rank q.k q.d m (tinyPhase p.g q.rank q.spJoint) coin warn
    (heatloss q.rank q.k) q.spear (bp (q.spJoint*(2* N)))

/-- The preparation schedule records only bounds already supplied by the
one-frame counting, closed-pin, phase, and injection calendars. -/
structure OnePlanted (q : PreparationParameters) (p : Shape) (M : ℕ) : Prop where
  early : OnePreparationAllows q
  hM : 1≤ M
  hg : Odd p.g
  hG : 3≤ p.g
  hJ : 1≤ p.j
  hR : 1≤ p.r
  hB : (q.B:ℝ)< bp ((p.b:ℝ)-2* p.j)
  exactRoom : 4* oneScreenRank p q.e+2* q.e* p.r< p.g* p.r
  wrap : ∀ᶠ n : ℕ in atTop,let N:=M* n;
    2* dim (OneFull p n)+3≤ N ∧ 4≤ N ∧
    (3*(onePreparationCover q):ℝ)*(2* N)≤((q.u:ℝ)-1)*(2* N) ∧
    (∀ (m : Mixer p n) (a : ImagePin (Comp p.g) (OneColumn p n) (2* N)),
      (onePinClosure p n).close a.sp=a.sp →
      pr (oneUnitRaw m N) (imagePinAgree oneCoordinateImages a)≤
        fee (2* N) ((q.ζ/6)/4) (imagePlanRank a.sp)) ∧
    oneIntern q p n N ∧ oneOutside q p n N

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M}
/-- Inside each pair of independently drawn leaves, every positive
compatibility probability has at least the specified mass. -/
def oneCompatibilityFloor (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N))
    (C : OneUnit p n N × OneUnit p n N → Prop) (γ : ℝ) :=
  ∀ i j : s.T,0< pr (pairW (partW w i.val) (partW w j.val)) C →
    γ≤ pr (pairW (partW w i.val) (partW w j.val)) C

variable {b : OneSketch p M}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : PreparationParameters}
structure OneSage (p : Shape) (n N : ℕ) where
  g : Bool→ OneAugur p N
  m : OneMarks p n N
  L : OneUnit p n N → Bool→ Finset (Label p.b)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis OneAppearance Function LinearMap Finset
open StatusAnalysis.DualAnalysis
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N c R : ℕ}
def OnePaletteGood (H : Space (OneJointKey p N)) (o : OneUnit p n N) : Prop :=
  ∀ i s,Injective ((oneMixedRow (oneFreeColumns p n s) (o i)).comp H.subtype)

def OneFullTableGap (Y : OneSilhouette p N c) (m : Mixer p n) (K : ℕ)
    (o o' : OneUnit p n N) : Prop :=
  ∀ d d',d≤ K^2→ d'≤ K^2→∀ i i',∀ v : Ax p n d,∀ v' : Ax p n d',
    (∀ j : Fin d,totalRank (v (Pi.single j 1))≤ K)→
    (∀ j : Fin d',totalRank (v' (Pi.single j 1))≤ K)→
    ∀ l q a b f f',
      (⟨l,a,f,q⟩ : Appearance p).apt→(⟨l,b,f',q⟩ : Appearance p).apt→
      ∀ z : Magazine p d,∀ z' : Magazine p d',z.1.sumBit=q→ z'.1.sumBit=q→
        let x : Appearance p:=⟨l,a,f,q⟩
        let y : Appearance p:=⟨l,b,f',q⟩
        let overlap:=avg (oneReference x Y) (fun j=>
          oneReflected x Y i o m v j z* oneReflected y Y i' o' m v' j z')
        overlap=0 ∨ bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))≤ overlap

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Finset PreparationParameters
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ} {q : PreparationParameters}
def exactPredictorRows (p : Shape) (q : PreparationParameters) := 2* oneScreenRank p q.e

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Function LinearMap Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
def oneGenericPostulates (o : OneOrient p n N) (g : OneAugur p N) (w : Pdual p n)
    (E : Finset (Label p.b)) (δ : ℝ):=
  ∀ s,s∉E→∀ l,pr (spins p n) (oneMismatch g w l s Flavor.full o)≤δ

def oneGenericSeems (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (x : OneUnit p n N) (g : Bool→ OneAugur p N) (z : Bool→ Profile p n)
    (L : Bool→ Finset (Label p.b)) (α : Party) (ε : ℝ):=
  (∀ i,(L i).card≤ q.B ∧ z i∈oneEffectivePins (oneEndpointPrimalPins (s.rooting x)) i) ∧
    ∀ i,oneGenericPostulates (x i) (g i) (oneYoke m x i (z i) (α i)) (L i) ε

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ} {q : PreparationParameters} {l : Filter ℕ}
  {m : cycleM p} {w : OneTale p M} {s : OneRhythms p M} {U : Ultrafilter ℕ}
  {b : OneSketch p M}
def oneBoundedLinearAugurs (p : Shape) (n N : ℕ) (g : Bool→ OneAugur p N):=
  ∃ R : ℕ,8* p.g* R≤ n ∧ ∀ i,OneLinearAugur (g i) R

def oneBoundedLinearPredicts (q : PreparationParameters) (m : Mixer p n)
    (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N)) (ε : ℝ):=
  ∃ g : Bool→ OneAugur p N,oneBoundedLinearAugurs p n N g ∧
    (0.000001:ℝ)≤ pr (s.sap w) (fun x=>∃ z L α,oneGenericSeems q m s x g z L α ε)

def oneLinearSilenceOutcome (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (s : OneRhythms p M):=
  ∃ ε : ℝ,0≤ε ∧ ∀ᶠ n in l,
    ¬oneBoundedLinearPredicts q (m n) (s n) (w n) ε ∧
      0.99< pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (oneSecureAt (s n))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter
open scoped Topology
noncomputable section
structure OneAnalyticParameters (p:Shape) (M:ℕ) (q:PreparationParameters) (s0:ℕ):Prop where
  planted:OnePlanted q p M
  unary:OneUnaryParameters p M (onePreparationPins q) s0
  thickness:4≤ M
  affine:p.j=1
  jump:1≤ p.J
  reserve:10* oneScalarBudget p (onePreparationPins q)+1000≤ q.B
  spare:3* q.B< Fintype.card (Label p.b)
  exactLateRoom:4* oneScreenRank p (onePreparationPins q)< p.g* p.r
  secure:∀ᶠ n:ℕ in atTop,OneEarnsScore p n (M* n) (onePreparationPins q) (2* q.ζ)

def oneConflicted {p:Shape} {n N:ℕ} (m:Mixer p n) (w:Wgt (OneUnit p n N)):=
  pr (pairW w w) (oneClash m)< bp (-200*(2* N:ℝ))

structure OneVeil (p:Shape) (M:ℕ) (q:PreparationParameters) (s0:ℕ)
    (l:Filter ℕ) (m:cycleM p) (s:OneRhythms p M) (w:OneTale p M):Prop where
  parameters:OneAnalyticParameters p M q s0
  time:l≤ atTop
  durable:OneDurable q l m w s
  moment:∀ᶠ n in l,OneNascent q (m n) (w n) ∧
    unaryGood (m n) (onePreparationPins q) s0 ∧ reducedBinaryGood (m n) ∧ oneConflicted (m n) (w n)

abbrev OneStations (p:Shape) (M K:ℕ) (s:OneRhythms p M):=
  ∀ n:ℕ,OneStation p n (M* n) K (s n)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter PreparationParameters PredictionClass Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev OneBranch := Option (PredictionClass × Party × F × Bool)

def preparationQuota (k : ℕ) : ℝ := 1 / ((k:ℝ)+1)

variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}
/-- Finite output of preparation at a single size. The rare case gives a
lower bound on positive conditional compatibility probabilities. -/
def OneBranchAt (q : PreparationParameters) (m : Mixer p n) (w : Wgt (OneUnit p n N))
    (s : OneLeafMixture p n N) (a : ℝ) : OneBranch → Prop
  | none => ¬oneBoundedLinearPredicts q m s w 0 ∧ 0.99< pr (pairW (s.sap w) (s.sap w)) (oneSecureAt s)
  | some (c,α,r,rare) => c.lit α ∧ ∃ i : OneSage p n N,
      OneAlgebraicRows i.g (exactPredictorRows p q) ∧ oneFiniteClass i.g α=c ∧
      s.within (fun x=> oneSeems q m s x i.g (i.m x) (i.L x) α 0 ∧
        glint p (i.m x)=r ∧ (c=dusk → oneExactInk m i.m x)) ∧
      let phases := oneMatchUp (fun x=> oneMarkedDelta x (i.m x)) α r c
      let law := pairW (s.sap w) (s.sap w)
      if rare then oneCompatibilityFloor s w phases a ∧ a/((2* N:ℕ):ℝ)^4≤ pr law phases ∧
          pr law (fun x=> phases x ∧ ¬oneSecureAt s x)≤0.001* pr law phases
      else a≤ pr law (fun x=> phases x ∧ oneSecureAt s x)

def OnePreparedAt (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) (k : ℕ) : Prop :=
  ∃ s : OneLeafMixture p n N,preparationQuota k≤ s.amount w ∧
    (oneLeafStrength s w m q.leafNew (2* q.ζ) (onePreparationPins q) ∧ s.within (oneFrameSide m)) ∧
    ∃ tag,OneBranchAt q m w s (preparationQuota k) tag

variable {m : cycleM p} {w : OneTale p M} {l : Filter ℕ}
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter Matrix PreparationParameters
open scoped BigOperators Topology
noncomputable section
namespace OneParameters
structure Complete (p:Shape) (M:ℕ) (b:PreparationParameters) (s0:ℕ):Prop
    extends OneAnalyticParameters p M b s0 where
  initial:∀ᶠ n:ℕ in atTop,∀ (m:Mixer p n) (w:Wgt (OneUnit p n (M* n))),
    OneNascent b m w → carried w (fun x=>(oneRawHoles m).unit (x true,x false)) →
    ∃ s:OneLeafMixture p n (M* n),OneEntered b m w s
  mixerRoom:s0≤ p.J

end OneParameters
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open Matrix Function Finset Module LinearMap Filter
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M r s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild
def trimBeta (p : Shape) (K:ℕ):=basebeta p K/2

structure Jubilee (p : Shape) (K:ℕ) (ε η:ℝ) : Prop where
  pos : 0<η
  book : playbook p K*η≤ε
  sturdyR : playbook p K*η<1/2* trimBeta p K^2
  low : 6*ε<1/2* trimBeta p K

variable {b:PreparationParameters}
end StatusAnalysis
end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters StatusAnalysis StatusAnalysis.DualAnalysis
open Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K M r s0:ℕ} {q:PreparationParameters}
  {pop:OneLeafMixture p n N} {m:Mixer p n}
structure OneLoupe (pop:OneLeafMixture p n N) (K:ℕ) where
  r:pop.T→ Stakes K

structure OneShipped (pop:OneLeafMixture p n N) (K:ℕ)
    (v:OneStation p n N K pop) (t:OneLoupe pop K):Prop where
  charts i:oneCharted (v.cAxes i (toRates (t.r i))) (pop.pin i.val).sp

def oneRouteC (t:OneLoupe pop K) (v:OneStation p n N K pop) (x:OneAspect pop):=
  v.cAxes x.1 (toRates (t.r x.1))

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Appearance StatusAnalysis.DualAnalysis OneAppearance Filter Finset Matrix Function LinearMap Module Template
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N K M r s0 : ℕ} {d : Rates}
def oneGenericSmoothSilk (p : Shape) (ε δ:ℝ) (Y:OneSilhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:OneOrient p n N) :=
    ∀ x : Appearance p,x.f=Flavor.full→
      (x.apt → oneClose x Y o ε) ∧ oneFoil x Y o m K δ

def oneGenericGauze (p : Shape) (ε δ:ℝ) (Y:OneSilhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:OneUnit p n N) :=
  ∀ i,oneGenericSmoothSilk p ε δ Y m K (o i)

namespace OneAppearance
variable (x : Appearance p) (Y : OneSilhouette p N r)
variable {d : ℕ}
end OneAppearance
namespace OneQuill
variable {q : Format} {d : Rates} {b : Bool}
def oneGeneric (w : Quill p q d b) : Prop:=∀ i,w.flav i=Flavor.full

end OneQuill
def oneGenericOption {q : Format} {d e : Rates} (w : Typus p q d e) : Prop :=
  OneQuill.oneGeneric w.qA ∧ OneQuill.oneGeneric w.qB

def oneGenericPermission {q : Format} {d e : Rates} (w : Typus p q d e) : Prop :=
  onePermission w ∧ oneGenericOption w

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K r:ℕ} {pop:OneLeafMixture p n N}
namespace OneStation
def genericEligiblePair (v:OneStation p n N K pop) (m:Mixer p n) (i j:OneAspect pop)
    (Y:OneSilhouette p N r) (a:ℝ):=
  ∃ k:OneScrip p K,(oneGenericPermission k.2.2) ∧ a≤ v.twilight k.2.2 m k.2.1 Y i.1 j.1 (i.2,j.2)

end OneStation
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter Finset Function
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}
structure OneGenericBeams {n N r K:ℕ} (m:Mixer p n) (Y:OneSilhouette p N r)
    (pop:OneLeafMixture p n N) (μ:Wgt (OneUnit p n N))
    (v:OneStation p n N K pop) (a ε δ τ:ℝ):Prop where
  soft:StatusAnalysis.DualAnalysis.origami p r (oneWisp p Y) δ
  rare:pr (pop.sap μ) (fun i=>¬oneGenericGauze p δ δ Y m K i)≤τ
  zone:pr (oneCirque pop μ) (fun x=> v.genericEligiblePair m x.1 x.2 Y a)≤τ
  haze:0<δ ∧ δ≤ε

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n N c R : ℕ}
def OneTesterFree (Y : OneSilhouette p N c) (f : Pulsar p c) : Prop :=
  ∀ l q q' k,oneFromPulse Y f l q k=oneFromPulse Y f l q' k

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function LinearMap Finset Matrix Submodule
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N r K c R : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}
open OneAppearance
def OneGenericStatusContinues (Y : OneSilhouette p N r) (m : Mixer p n) (B : ℕ)
    (o : OneUnit p n N) : Prop :=
  ∀ d : Rates,∀ v : Charts p n d,
    ∀ i E,E.card≤ B→∀ a f,
      GenericStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i E a f→
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i ∅ a f

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
noncomputable section
open Filter Matrix Module LinearMap Finset Function
open scoped BigOperators Topology
open Template
open StatusAnalysis
namespace OneExactOptions
open PreparationParameters OneStation PredictionClass Club Guild DualAnalysis
variable {p : Shape} {n N M r s0 K coords : ℕ} {w:OneLeafMixture p n N} {b:PreparationParameters}
def witnessed (w : OneLeafMixture p n N) (v : OneStation p n N K w) (L : OneLoupe w K)
    (m : Mixer p n) (Y : OneSilhouette p N r) (H : Space (OneJointKey p N))
    (B : ℕ) (cat : Nodes→ Pulsar p r) (x : OneAspect w) :=
  OnePaletteGood H x.2 ∧ ExactAnnounced (oneWisp p Y)
    (oneWake p Y m x.2 (oneRouteC L v x)) cat B

end OneExactOptions
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix Submodule LinearMap
open scoped BigOperators
noncomputable section
variable {d e : ℕ}
abbrev PredictedTriple := F × F × F

def predictedGenerator (α β : F) (X : Cell d) (Y : Cell e)
    (r : PredictedTriple) (u : Par d) (v : Par e) : Signal d e :=
  (r.1,(u,dotProduct X u.2+α* u.1+r.2.1),(v,dotProduct Y v.2+β* v.1+r.2.2))

def predictedSpan (α β : F) (X : Cell d) (Y : Cell e) (R : Set PredictedTriple) :
    Space (Signal d e) :=
  Submodule.span F {s | ∃ r ∈ R, ∃ u v, s=predictedGenerator α β X Y r u v}

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass
open Finset Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N r : ℕ} {A B : Rates}
def retainedPatterns (u : Terrain p r) (f : Bool → Pulsar p r) (η : ℝ)
    (i : Grid) : Set PredictedTriple :=
  {v | ∃ (l : Tag p.g) (k : Fin r), η ≤ u l v.1 k ∧
    v.2.1=f i.1 l v.1 k ∧ v.2.2=f i.2 l v.1 k}

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass Template
open Finset Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {N r : ℕ}
def predictorCellCount : ℕ := Fintype.card (F×F)

def predictorPulse (c : PredictionClass) : Bool → Pulsar p predictorCellCount :=
  fun i _ _ k => if c=dusk then 0 else if i then
    ((Fintype.equivFin (F×F)).symm k).1 else ((Fintype.equivFin (F×F)).symm k).2

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {N r s:ℕ} {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
structure OnePaint (t:Tagging p I) (N:ℕ) where
  coeff:ℝ
  flies:∀ i,OneAtomKey (p:=p) (t i) N→ Prop

def oneMural {t:Tagging p I} (F:J→ OnePaint t N):Wgt (OneKeys t N):=
  fun x=>∑ j,(F j).coeff*∏ i,ind ((F j).flies i (x i))

def OneDesign (t:Tagging p I) (W:Wgt (OneKeys t N)) (k:ℕ):Prop:=
  ∃ F:Fin k→ OnePaint t N,W=oneMural F ∧ ∀ j,|(F j).coeff|≤1

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass Template Filter
open Finset Matrix Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {N r:ℕ}
def onePreparedPredictor (c:PredictionClass) (g:Bool→ OneAugur p N):Bool→ OneAugur p N:=
  if c=dusk then 0 else g

def onePredictorPartition (c:PredictionClass) (g:Bool→ OneAugur p N):
    OneSilhouette p N predictorCellCount:=
  fun l q k=> Fintype.equivFin (F×F)
    (onePreparedPredictor c g true l q k,onePreparedPredictor c g false l q k)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass
open Matrix Finset Function LinearMap Module
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N r:ℕ} {A B:Rates}
def oneCoordSpec (m:OneUnit p n N→ Bool→ Profile p n) (o:OneUnit p n N)
    (s:Charts p n A) (g:∀ i,Cell (A i)):=∀ i,s i (g i)=m o i

def oneCardTone (m:OneUnit p n N→ Bool→ Profile p n) (x:OneUnit p n N)
    (T:OneCross p n) (j:Bool):F:=∑ i:Bool,oneContract T i j (m x i)

end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis OneAppearance Template Filter Finset Matrix Function
open scoped BigOperators Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {n N K r:ℕ}
variable (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→ F)
def oneBaseDeposit (m:Mixer p n) (o:OneUnit p n N) (s:Charts p n d)
    (x:Inputs p n (Messenger q)):Prop:=
  (∀ i,w.sameInk i (onePrinted b s t w.sel w.flav m o x i)) ∧
    ((w.pen t).draw x).reads (reducedScript w.script) m ∧
      oneOwnKeyPart t z (oneVolleyKeys ((w.pen t).draw x) t o)

def oneBaseProwl (s:Charts p n d) (m:Mixer p n) (o:OneUnit p n N)
    (W:Wgt (OneKeys t N)):=
  avg ((w.pen t).state z n) (fun x=> ind (oneBaseDeposit w t z m o s x)*
    W (oneVolleyKeys ((w.pen t).draw x) t o))

structure OneBaseSteady (m:Mixer p n) (K:ℕ) (s:Charts p n d)
    (o:OneUnit p n N):Prop where
  frame:∀ i,oneFrameLaw m (o i)
  steadyAxes (i:Messenger q):Quill.prelim (b:=b) K s i
  enough (i:Messenger q):(w.amp i).1.diagO=(w.amp i).2.1.1
  generic:oneGeneric w

def oneDilate (K:ℕ):=oneKappa (w.pen t)*(basebeta p K/2)^Fintype.card (Messenger q)

end OneQuill
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {K s0:ℕ}
def OneBaseSober {n N:ℕ} (w:Quill p q d b) (t:Tagging p (Messenger q))
    (z:Messenger q→ F) (K:ℕ) (H:OneKeys t N→ Prop) (m:Mixer p n) (α:ℝ)
    (o:OneUnit p n N):=
  ∀ s:Charts p n d,OneBaseSteady w m K s o →
    α≤ oneBaseProwl w t z s m o (fun k=> ind (H k))

end OneQuill
end
end Lax793645.ConstructionData.Frames
end

section
namespace Lax793645.ConstructionData.Binary
noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Real Filter
def ord (g N : ℕ) := (2:ℕ)^(1000* g* N)

end HadwigerCounterexample
end
end Lax793645.ConstructionData.Binary
end

section
namespace Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Filter Finset PreparationParameters
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneConstruction
variable {p:Shape} {n N M s0:ℕ} {b:PreparationParameters}
def conflictLowerBound (m:Mixer p n) (N:ℕ) (b:PreparationParameters):=
  ∀ w:Wgt (OneUnit p n N),OneNascent b m w →
    carried w (fun x=>(oneRawHoles m).unit (x true,x false)) →
    bp (-200*(2* N:ℝ))≤ pr (pairW w w) (oneClash m)

open HadwigerMatching
end OneConstruction
end
end Lax793645.ConstructionData.Frames
end
