import Lax793645Proofs.Simplifications.QuadraticMomentMaps
import Lax793645Proofs.Simplifications.HyperbolicCoordinates
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AffineFrames

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- N is half the ambient dimension. The primal frame is stored once. -/
abbrev OneFrame (p : Shape) (n N : ℕ) :=
  QuadraticFull (Ray p n) (Vec (Fin p.h))→ₗ[F]Vec (HyperbolicIdx N)
abbrev OneOrient (p : Shape) (n N : ℕ) := Comp p.g→OneFrame p n N
abbrev OneAmbient (p : Shape) (N : ℕ) :=
  Comp p.g→Mat (HyperbolicIdx N) (HyperbolicIdx N)

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

theorem one_functional_self {m : Mixer p n} {o : OneOrient p n N}
    (ho : oneFrameLaw m o) (x : Profile p n) : oneFunctional o (oneMomentEmbed o x)=0 := by
  apply Finset.sum_eq_zero
  intro e _
  apply quadratic_channel_self
  intro j v
  exact (quadratic_channel_frame_data _ _ _ (ho e)).2.2 (Pi.single j 1) v

theorem moment_square_span {W : Moment p n} (hW : W∈Wspace p n) :
    W∈quadraticSquares (⊤ : Space (Ray p n)) := by
  apply (Submodule.span_le.mpr ?_) hW
  rintro M ⟨s,z,rfl⟩
  exact Submodule.subset_span ⟨point p s z,Submodule.mem_top,rfl⟩

/-- This is the invariant replacing the ordered two-frame self Gram. -/
theorem one_moment_tester {m : Mixer p n} {o : OneOrient p n N}
    (hj : 1≤p.j) (ho : oneFrameLaw m o) (e : Comp p.g)
    {W : Moment p n} (hW : W∈Wspace p n) :
    mpair (hyperbolicMatrix N) (quadraticMomentMap (onePrimal (o e)) W)=eta p n W := by
  rw [quadratic_moment_invariant (onePrimal (o e)) (hyperbolicMatrix N)
    (selfM p n m.mixM) (ho e).2.1 (moment_square_span hW)]
  exact selfM_pair p hj _ hW

theorem one_common_image_tester {m : Mixer p n} {o o' : OneOrient p n N}
    (hj : 1≤p.j) (ho : oneFrameLaw m o) (ho' : oneFrameLaw m o')
    {x y : Profile p n} (hx : x∈Xspace p n) (hy : y∈Xspace p n)
    (he : oneMomentEmbed o x=oneMomentEmbed o' y) (e : Comp p.g) :
    eta p n (x e)=eta p n (y e) := by
  have component_mem {z : Profile p n} (hz : z∈Xspace p n) : z e∈Wspace p n := by
    obtain ⟨w,hw,rfl⟩:=mem_X.mp hz
    exact (Wspace p n).add_mem (Wtag_le _ (hw _)) (Wtag_le _ (hw _))
  rw [←one_moment_tester hj ho e (component_mem hx),
    ←one_moment_tester hj ho' e (component_mem hy)]
  exact congrArg (mpair (hyperbolicMatrix N)) (congrFun he e)

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
end Lax793645Proofs.Simplifications
