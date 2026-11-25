import Lax793645Proofs.Simplifications.OnePredictionClasses

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
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
  ∀ l q x,g l q x=r*q

def oneInactive (g : Bool→OneAugur p N) (α : Party) (i : Bool) :=
  firstBit α i=0 ∧ ∃ r,oneLiteral (g i) r

def oneCoincident (g : Bool→OneAugur p N) (α : Party) :=
  α true=α false ∧ ∃ r,oneLiteral (oneAssembly g true false 1 1) r

def oneFiniteClass (g : Bool→OneAugur p N) (α : Party) : PredictionClass := by
  classical
  exact if oneInactive g α true then
    if oneInactive g α false then dusk else dawn false
  else if oneInactive g α false then dawn true
  else if oneCoincident g α then twinned else noon

theorem one_finite_active (g : Bool→OneAugur p N) (α : Party) (i : Bool) :
    (oneFiniteClass g α).active i ↔ ¬oneInactive g α i := by
  classical
  unfold oneFiniteClass
  cases i <;> split_ifs <;> simp_all [active]

theorem one_finite_lit (g : Bool→OneAugur p N) (α : Party) :
    (oneFiniteClass g α).lit α := by
  classical
  constructor
  · intro i hi
    exact (show oneInactive g α i from not_not.mp
      (fun h=>hi ((one_finite_active g α i).mpr h))).1
  unfold oneFiniteClass
  intro h
  split_ifs at h <;> try contradiction
  exact ‹oneCoincident g α›.1

theorem one_literal_add {g h : OneAugur p N} {r s : F}
    (hg : oneLiteral g r) (hh : oneLiteral h s) :
    oneLiteral (fun l q x=>g l q x+h l q x) (r+s) := by
  intro l q x
  change g l q x+h l q x=(r+s)*q
  rw [hg,hh,add_mul]

theorem one_finite_match {g : Bool→OneAugur p N} {α : Party}
    (h : oneCoincident g α) : oneInactive g α true ↔ oneInactive g α false := by
  obtain ⟨ha,s,hs⟩:=h
  have hs : oneLiteral (fun l q x=>g true l q x+g false l q x) s := by
    simpa only [oneLiteral,oneAssembly,one_mul] using hs
  constructor
  · rintro ⟨h,r,hr⟩
    refine ⟨by simpa only [firstBit,←ha] using h,r+s,?_⟩
    have hh:=one_literal_add hr hs
    intro l q x
    simpa only [←add_assoc,char_two,zero_add] using hh l q x
  · rintro ⟨h,r,hr⟩
    refine ⟨by simpa only [firstBit,ha] using h,r+s,?_⟩
    have hh:=one_literal_add hr hs
    intro l q x
    have hval:=hh l q x
    change g false l q x+(g true l q x+g false l q x)=(r+s)*q at hval
    rw [add_left_comm,char_two,add_zero] at hval
    exact hval

theorem one_finite_echoes (g : Bool→OneAugur p N) (α : Party)
    (i j : Bool) (s t r : F) (h : s*firstBit α i=t*firstBit α j)
    (hg : oneLiteral (oneAssembly g i j s t) r) :
    (oneFiniteClass g α).echoes i j s t := by
  classical
  unfold echoes
  simp_rw [one_finite_active]
  rcases bit_cases s with hs|hs <;> rcases bit_cases t with ht|ht <;> subst s t
  · simp
  · have hi : firstBit α j=0 := by simpa only [zero_mul,one_mul] using h.symm
    have hh : oneLiteral (g j) r := by
      simpa only [oneLiteral,oneAssembly,zero_mul,one_mul,zero_add] using hg
    have he : oneInactive g α j:=⟨hi,r,hh⟩
    simp [he]
  · have hi : firstBit α i=0 := by simpa only [zero_mul,one_mul] using h
    have hh : oneLiteral (g i) r := by
      simpa only [oneLiteral,oneAssembly,zero_mul,one_mul,add_zero] using hg
    have he : oneInactive g α i:=⟨hi,r,hh⟩
    simp [he]
  simp only [true_and]
  by_cases hij : i=j
  · subst j
    simp
  have hc : oneCoincident g α := by
    have hh : 1+α i=1+α j := by simpa only [one_mul,firstBit] using h
    have ha : α i=α j:=add_left_cancel hh
    have he : oneAssembly g i j 1 1=oneAssembly g true false 1 1 := by
      funext l q x
      simp only [oneAssembly,one_mul]
      cases i <;> cases j <;> first | rfl | contradiction | exact add_comm _ _
    refine ⟨?_,r,he ▸ hg⟩
    cases i <;> cases j <;> first | contradiction | exact ha | exact ha.symm
  have hm:=one_finite_match hc
  by_cases he : oneInactive g α true
  · have hh (i : Bool) : oneInactive g α i := by cases i; exact hm.mp he; exact he
    simp [hh]
  have hh (i : Bool) : ¬oneInactive g α i := by cases i; exact mt hm.mpr he; exact he
  simp only [oneFiniteClass,if_neg (hh _),if_pos hc]
  simp [hh]

/-- A uniform finite separation test replaces all limits of disagreement
probabilities in prediction classification. -/
theorem one_finite_recital (g : Bool→OneAugur p N) (α : Party) (τ : ℝ)
    (hgap : ∀ i j s t r,
      (∀ l q,oneTabRef p l q (oneAssembly g i j s t) r≤τ) →
        oneLiteral (oneAssembly g i j s t) r) :
    oneRecital (oneFiniteClass g α) g α τ := by
  refine ⟨one_finite_lit g α,?_⟩
  intro i j s t r he hr
  apply one_finite_echoes g α i j s t r he
  apply hgap i j s t r
  intro l q
  have hh:=hr l q
  change tabRef p l q (oneAugurCoordinates (oneAssembly g i j s t)) r≤τ at hh
  simpa only [←one_tab_reference_coordinates] using hh

theorem one_finite_dusk (g : Bool→OneAugur p N) (α : Party)
    (h : oneFiniteClass g α=dusk) (i : Bool) :
    firstBit α i=0 ∧ ∃ r,oneLiteral (g i) r := by
  have hh : ¬(oneFiniteClass g α).active i := by rw [h]; exact not_false
  exact not_not.mp (fun hi=>hh ((one_finite_active g α i).mpr hi))

end
end Lax793645Proofs.Simplifications
