import Lax793645Proofs.Simplifications.CycleComponents

/-! Component indices for the odd-cycle construction. -/
namespace Lax793645Proofs.Upstream.OAI
noncomputable section
namespace HadwigerCounterexample

abbrev Tag := Fin
abbrev Comp := Lax793645Proofs.Simplifications.CycleGeometry.Comp
abbrev tagDegree := Lax793645Proofs.Simplifications.CycleGeometry.degree
def inc {g : ℕ} (e : Comp g) (l : Tag g) := e.val.1=l ∨ e.val.2=l
instance {g : ℕ} (e : Comp g) (l : Tag g) : Decidable (inc e l) :=
  inferInstanceAs (Decidable (_ ∨ _))
abbrev TagStar {g : ℕ} (l : Tag g) := {e : Comp g // inc e l}

variable {g : ℕ}

theorem card_star (l : Tag g) : Fintype.card (TagStar l)=tagDegree g :=
  Lax793645Proofs.Simplifications.CycleGeometry.card_star l

theorem tagDegree_pos (h : 2≤g) : 0<tagDegree g := by
  unfold tagDegree Lax793645Proofs.Simplifications.CycleGeometry.degree
  omega

/-- A private ordinary block belongs only to its owner.  Empty degenerate
geometries retain no ordinary block. -/
def allowed (d l : Tag g) := 1<g ∧ d=l
instance (d l : Tag g) : Decidable (allowed d l) :=
  inferInstanceAs (Decidable (_ ∧ _))

def privateWidth (g : ℕ) := min 1 (g-1)

theorem privateWidth_of_two_le (h : 2≤g) : privateWidth g=1 := by
  unfold privateWidth; omega

theorem card_allowed (d : Tag g) :
    Fintype.card {l : Tag g // allowed d l}=privateWidth g := by
  classical
  by_cases hg : 1<g
  · simp [allowed,hg,privateWidth_of_two_le hg]
  · simp [allowed,hg,privateWidth]
    omega

theorem card_allowed' (l : Tag g) :
    Fintype.card {d : Tag g // allowed d l}=privateWidth g := by
  classical
  by_cases hg : 1<g
  · simp [allowed,hg,privateWidth_of_two_le hg]
  · simp [allowed,hg,privateWidth]
    omega

end HadwigerCounterexample
end
end Lax793645Proofs.Upstream.OAI
