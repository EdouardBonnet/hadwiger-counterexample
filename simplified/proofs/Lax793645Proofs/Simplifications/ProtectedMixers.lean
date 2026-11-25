import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MixerConditions
import Mathlib.Tactic

/-! Overwriting entries away from Z preserves the actual unary polar matrices
of the vendored construction, including their dependence on arbitrary profiles. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def agreesAt (P : I → Prop) (A B : Mat I I) : Prop :=
  ∀ i j, P i ∨ P j → A i j = B i j

def protectedPatch (P : I → Prop) (A B : Mat I I) : Mat I I := by
  classical
  exact fun i j => if P i ∨ P j then A i j else B i j

omit [Fintype I] in
theorem protectedPatch_agrees (P : I → Prop) (A B : Mat I I) :
    agreesAt P A (protectedPatch P A B) := by
  classical
  intro i j h
  simp [protectedPatch, h]

omit [Fintype I] in
theorem agreesAt_transpose {P : I → Prop} {A B : Mat I I} (h : agreesAt P A B) :
    agreesAt P A.transpose B.transpose := by
  intro i j hij
  exact h j i hij.symm

omit [Fintype J] in
theorem protected_left {P : I → Prop} {A B : Mat I I} (h : agreesAt P A B)
    (Q : Mat I J) (hQ : ∀ i j, ¬P i → Q i j = 0) : Q.transpose*A=Q.transpose*B := by
  classical
  ext i j
  apply Finset.sum_congr rfl
  intro k _
  change Q k i * A k j = Q k i * B k j
  by_cases hk : P k
  · rw [h k j (Or.inl hk)]
  · simp [hQ k i hk]

omit [Fintype J] in
theorem protected_pull_lift {P : I → Prop} {A B C D : Mat I I}
    (hAB : agreesAt P A B) (hCD : agreesAt P C D)
    (Q : Mat I J) (hQ : ∀ i j, ¬P i → Q i j = 0) (X : Mat I I) :
    pullM Q Q (liftM A C X) = pullM Q Q (liftM B D X) := by
  have h1 := protected_left hAB Q hQ
  have h2 := congrArg Matrix.transpose (protected_left hCD Q hQ)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h2
  simp only [pullM_def, liftM_def]
  calc
    Q.transpose * (A * X * C.transpose) * Q =
      (Q.transpose*A)*X*(C.transpose*Q) := by simp only [Matrix.mul_assoc]
    _ = (Q.transpose*B)*X*(D.transpose*Q) := by rw [h1, h2]
    _ = Q.transpose*(B*X*D.transpose)*Q := by simp only [Matrix.mul_assoc]

variable {p : Shape} {n : ℕ}

def isZRow (i : Row p n) : Prop := ∃ k, i.2 = some (Block.Z, k)

theorem blockRay_Z_support (s : Label p.b) (i : Row p n) (j : Fin n)
    (h : ¬isZRow i) : blockRay p n s Block.Z i j = 0 := by
  rw [blockRay_eval]
  exact if_neg (fun he => h ⟨j, he⟩)

def sameZMixers (m m' : Mixer p n) : Prop :=
  (∀ j e f, agreesAt isZRow (m.mixL j e f) (m'.mixL j e f)) ∧
  (∀ j e f, agreesAt isZRow (m.mixR j e f) (m'.mixR j e f))

theorem unary_qmix_preserved (m m' : Mixer p n) (h : sameZMixers m m')
    (x : Profile p n) (l : Tag p.g) (s : Label p.b) :
    pullM (blockRay p n s Block.Z) (blockRay p n s Block.Z) (qmix m x l) =
    pullM (blockRay p n s Block.Z) (blockRay p n s Block.Z) (qmix m' x l) := by
  simp only [qmix, map_sum, map_add]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro e _
  rw [protected_pull_lift (agreesAt_transpose (h.1 j e f.val))
      (agreesAt_transpose (h.2 j e f.val)) _ (blockRay_Z_support s) (x e),
    protected_pull_lift (h.1 j f.val e) (h.2 j f.val e) _ (blockRay_Z_support s) (x e)]

omit [Fintype J] in
theorem pull_transpose (Q : Mat I J) (A : Mat I I) :
    pullM Q Q A.transpose = (pullM Q Q A).transpose := by
  simp only [pullM_def, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- A genuine preservation theorem for the existing `unaryGood` predicate. -/
theorem unaryGood_preserved (m m' : Mixer p n) (h : sameZMixers m m') (K s0 : ℕ)
    (hm : unaryGood m K s0) : unaryGood m' K s0 := by
  intro x l s hx hpos
  have he := unary_qmix_preserved m m' h x l s
  have hb : blockRank Block.Z s s (qmix m x l + (qmix m x l).transpose) =
      blockRank Block.Z s s (qmix m' x l + (qmix m' x l).transpose) := by
    simp only [blockRank, map_add, pull_transpose, he]
  rw [← hb]
  exact hm x l s hx hpos

end
end Lax793645Proofs.Simplifications
