import Lax793645Proofs.Simplifications.QuadraticOrbitLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
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

theorem quadratic_channel_class_exists (Q : QuadraticForm QField B) :
    ∃ A : QuadraticForm QField (QuadraticFull B C),quadraticChannelClass Q A := by
  refine ⟨Q.comp (LinearMap.fst QField B (C×C)),?_,?_⟩
  · apply QuadraticMap.ext
    intro b
    rfl
  · intro c b
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,quadraticXIn,
      quadraticPrimalIn,QuadraticMap.comp_apply]

def quadraticChannelValid (q : QuadraticForm QField V) (Q : QuadraticForm QField B)
    (P : QuadraticFull B C→ₗ[QField]V) :=
  quadraticFramesAt q (quadraticChannelClass Q) P

theorem quadratic_channel_frame_data (q : QuadraticForm QField V)
    (Q : QuadraticForm QField B) (P : QuadraticFull B C→ₗ[QField]V)
    (hP : quadraticChannelValid q Q P) :
    Function.Injective P ∧ (∀ b,q (P (quadraticPrimalIn b))=Q b) ∧
      ∀ c b,q.polarBilin (P (quadraticXIn c)) (P (quadraticPrimalIn b))=0 := by
  refine ⟨hP.1,fun b=>congrArg (fun A : QuadraticForm QField B=>A b) hP.2.1,?_⟩
  intro c b
  have hh:=hP.2.2 c b
  simpa only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    QuadraticMap.comp_apply,map_add] using hh

theorem quadratic_channel_frames_exist [FiniteDimensional QField B]
    [FiniteDimensional QField C] [FiniteDimensional QField V]
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (Q : QuadraticForm QField B)
    (hroom : 2*(Module.finrank QField B+2*Module.finrank QField C)+2≤Module.finrank QField V) :
    ∃ P : QuadraticFull B C→ₗ[QField]V,quadraticChannelValid q Q P := by
  apply quadratic_frames_exists q hnd _ (quadratic_channel_class_exists Q)
  simpa only [QuadraticFull,Module.finrank_prod,two_mul,add_assoc] using hroom

def quadraticChannelRaw [Fintype (QuadraticFull B C→ₗ[QField]V)]
    (q : QuadraticForm QField V) (Q : QuadraticForm QField B) :
    Wgt (QuadraticFull B C→ₗ[QField]V):=unifOn (quadraticChannelValid q Q)

theorem quadratic_channel_raw_law [FiniteDimensional QField B]
    [FiniteDimensional QField C] [FiniteDimensional QField V]
    [Fintype (QuadraticFull B C→ₗ[QField]V)]
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (Q : QuadraticForm QField B)
    (hroom : 2*(Module.finrank QField B+2*Module.finrank QField C)+2≤Module.finrank QField V) :
    IsLaw (quadraticChannelRaw (C:=C) q Q) :=
  unifOn_law (quadratic_channel_frames_exist q hnd Q hroom)

/-- A batch of independent nominal primal columns has precisely the uniform
quadratic-Gram law, even though the own-frame channel constraints are present. -/
theorem quadratic_channel_primal_observe [FiniteDimensional QField B]
    [FiniteDimensional QField C] [FiniteDimensional QField R] [FiniteDimensional QField V]
    [Fintype (QuadraticFull B C→ₗ[QField]V)] [Fintype (R→ₗ[QField]V)]
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (Q : QuadraticForm QField B) (J : R→ₗ[QField]B) (hJ : Function.Injective J)
    (hroom : 2*(Module.finrank QField B+2*Module.finrank QField C)+2≤Module.finrank QField V)
    (hbatch : 2*Module.finrank QField R+6≤Module.finrank QField V) :
    mapW (quadraticChannelRaw (C:=C) q Q)
      (fun P=>P.comp (quadraticPrimalIn.comp J))=unifOn (quadraticGramGood q (Q.comp J)) := by
  unfold quadraticChannelRaw quadraticChannelValid
  refine quadratic_frames_observe q hnd (quadraticChannelClass (C:=C) Q)
    (quadratic_channel_frames_exist q hnd Q hroom) (quadraticPrimalIn.comp J)
    ?_ (Q.comp J) ?_ hbatch
  · intro x y h
    exact hJ (congrArg Prod.fst h)
  · intro A hA
    exact congrArg (fun Q : QuadraticForm QField B=>Q.comp J) hA.1

end
end Lax793645Proofs.Simplifications
