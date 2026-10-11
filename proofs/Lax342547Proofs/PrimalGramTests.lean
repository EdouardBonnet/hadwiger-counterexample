import Lax342547.PrimalGramTests
import Lax342547.ComponentTests
import Lax342547.PrimalRecords
import Lax342547.RetainedCharacters

namespace Lax342547Proofs.PrimalGramTests
open Lax342547.PrimalGramTests

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TableSpaces
open Lax342547.TableContractions Lax342547.RawContractions Lax342547.ReferencePins
open Lax342547.ProductImages Lax342547.RetainedCharacters Lax342547.CoefficientPhase
open Lax342547.ComponentTests Lax342547.PrimalRecords Lax342547.RawFrames

/--
---
conclusion: Lax342547.PrimalGramTests.gram_form_evaluation
---
-/
theorem gram_form_evaluation {I N : Type} [Fintype I] [Fintype N]
    (X Y : Matrix N I Binary) (u v : I → Binary) :
    actualForm X Y u v = dotProduct (X.mulVec u) (Y.mulVec v) := by
  classical
  unfold actualForm
  rw [Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

/--
---
conclusion: Lax342547.PrimalGramTests.raw_oriented_forms
---
-/
theorem raw_oriented_forms {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (oA oB : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) :
    actualForm (leftMatrices oA a) (rightMatrices oB a) = orientedForms (rawForms oA oB) a := by
  classical
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rw [Lax342547.PrimalGramTests.gram_form_evaluation]
  rcases a with ⟨e,s⟩
  cases s
  · change dotProduct _ _ = dotProduct _ _
    rw [dotProduct_comm]
    rfl
  · rfl

/--
---
conclusion: Lax342547.PrimalGramTests.matrix_pair_outer
---
-/
theorem matrix_pair_outer {I : Type} [Fintype I]
    (T : LinearMap.BilinForm Binary (I → Binary)) (u v : I → Binary) : by
      classical
      exact matrixPair (LinearMap.BilinForm.toMatrix' T) (Matrix.vecMulVec u v) = T u v := by
  classical
  conv_rhs => rw [← Matrix.toBilin'_toMatrix' T, Matrix.toBilin'_apply]
  unfold matrixPair
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, matrixEntry, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax342547.PrimalGramTests.entry_target_bits
---
-/
theorem entry_target_bits {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) : targetBits entryTests (orientedForms F) = entries F := by
  classical
  funext t
  unfold targetBits
  simp only [entryTests, apply_ite, map_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, Lax342547.PrimalGramTests.matrix_pair_outer]
  rcases t with ⟨dir,mode,e,i,z,b,h⟩
  fin_cases dir <;> fin_cases mode <;>
    simp [entryAxis, entryLeft, entryRight, orientedForms, entries, CrossForms.flip, fullPlus, fullMinus]

/--
---
conclusion: Lax342547.PrimalGramTests.entry_actual_bits
---
-/
theorem entry_actual_bits {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (oA oB : Fin 2 → Comp → Frame B H N E) :
    actualBits entryTests (leftMatrices oA) (rightMatrices oB) = entries (rawForms oA oB) := by
  classical
  rw [← Lax342547.PrimalGramTests.entry_target_bits]
  funext t
  unfold actualBits targetBits
  simp only [Lax342547.RetainedCharacters.coefficient_pair_form, Lax342547.PrimalGramTests.raw_oriented_forms]

/--
---
conclusion: Lax342547.PrimalGramTests.primal_entry_agreement
---
-/
theorem primal_entry_agreement {ΩA ΩB Comp B H N : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    {M : Matrix B B Binary}
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (unitA : ΩA → Fin 2 → Comp → Frame B H N M)
    (unitB : ΩB → Fin 2 → Comp → Frame B H N M)
    (D E : Comp × Bool → Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary))
    (F : CrossForms Comp B H)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hαsum : ∑ x, α x = 1) (hβsum : ∑ y, β y = 1)
    (hD : ∀ x y a v, v ∈ D a → ∀ w,
      actualForm (leftMatrices (unitA x) a) (rightMatrices (unitB y) a) v w = orientedForms F a v w)
    (hE : ∀ x y a v w, w ∈ E a →
      actualForm (leftMatrices (unitA x) a) (rightMatrices (unitB y) a) v w = orientedForms F a v w)
    (hcapA : ∀ (r : Comp × Bool → ℕ)
      (A : ∀ a, Matrix (Fin 2 × (B ⊕ H)) (Fin (r a)) Binary),
      (∀ a, Function.Injective ((D a).mkQ.comp (A a).mulVecLin)) →
      ∀ x, Lax342547.PushforwardWalsh.push α
        (fun ω => Lax342547.ComponentCharacters.blockImage A (leftMatrices (unitA ω))) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, r a)*Fintype.card N)))
    (hcapB : ∀ (r : Comp × Bool → ℕ)
      (A : ∀ a, Matrix (Fin 2 × (B ⊕ H)) (Fin (r a)) Binary),
      (∀ a, Function.Injective ((E a).mkQ.comp (A a).mulVecLin)) →
      ∀ x, Lax342547.PushforwardWalsh.push β
        (fun ω => Lax342547.ComponentCharacters.blockImage A (rightMatrices (unitB ω))) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, r a)*Fintype.card N)))
    (hsmall : (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N) ≤
      1 / (2 : ℝ)^(16 * Fintype.card Comp * Fintype.card H * Fintype.card B + 1)) :
    1 / (2 : ℝ)^(16 * Fintype.card Comp * Fintype.card H * Fintype.card B + 1) ≤
      Lax342547.FourierTests.patternMass (fun ab : ΩA × ΩB => α ab.1 * β ab.2)
        (fun ab => entries (rawForms (unitA ab.1) (unitB ab.2))) (entries F) := by
  classical
  have h := Lax342547.ComponentTests.component_scalar_agreement α β
    (fun x => leftMatrices (unitA x)) (fun y => rightMatrices (unitB y))
    D E (orientedForms F) hα hβ hαsum hβsum hD hE hcapA hcapB entryTests
    (by simpa only [Lax342547.PrimalRecords.entry_count] using hsmall)
  simpa only [Lax342547.PrimalGramTests.entry_actual_bits, Lax342547.PrimalGramTests.entry_target_bits, Lax342547.PrimalRecords.entry_count] using h

/--
---
conclusion: Lax342547.PrimalGramTests.primal_cell_four_holes
---
-/
theorem primal_cell_four_holes {ΩA ΩB H N : Type} {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    [Fintype ΩA] [Fintype ΩB] [Fintype H] [Fintype N]
    {M : Lax342547.ConcreteGeometry.Moment k n b degree}
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (unitA : ΩA → Fin 2 → Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) → Frame (Lax342547.ConcreteGeometry.Coordinate k n b degree) H N M)
    (unitB : ΩB → Fin 2 → Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) → Frame (Lax342547.ConcreteGeometry.Coordinate k n b degree) H N M)
    (D E : Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) × Bool → Submodule Binary ((Fin 2 × (Lax342547.ConcreteGeometry.Coordinate k n b degree ⊕ H)) → Binary))
    (F : CrossForms (Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k)) (Lax342547.ConcreteGeometry.Coordinate k n b degree) H)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hαsum : ∑ x, α x = 1) (hβsum : ∑ y, β y = 1)
    (hD : ∀ x y a v, v ∈ D a → ∀ w,
      actualForm (leftMatrices (unitA x) a) (rightMatrices (unitB y) a) v w = orientedForms F a v w)
    (hE : ∀ x y a v w, w ∈ E a →
      actualForm (leftMatrices (unitA x) a) (rightMatrices (unitB y) a) v w = orientedForms F a v w)
    (hcapA : ∀ (r : Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) × Bool → ℕ)
      (A : ∀ a, Matrix (Fin 2 × (Lax342547.ConcreteGeometry.Coordinate k n b degree ⊕ H)) (Fin (r a)) Binary),
      (∀ a, Function.Injective ((D a).mkQ.comp (A a).mulVecLin)) →
      ∀ x, Lax342547.PushforwardWalsh.push α
        (fun ω => Lax342547.ComponentCharacters.blockImage A (leftMatrices (unitA ω))) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, r a)*Fintype.card N)))
    (hcapB : ∀ (r : Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) × Bool → ℕ)
      (A : ∀ a, Matrix (Fin 2 × (Lax342547.ConcreteGeometry.Coordinate k n b degree ⊕ H)) (Fin (r a)) Binary),
      (∀ a, Function.Injective ((E a).mkQ.comp (A a).mulVecLin)) →
      ∀ x, Lax342547.PushforwardWalsh.push β
        (fun ω => Lax342547.ComponentCharacters.blockImage A (rightMatrices (unitB ω))) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, r a)*Fintype.card N)))
    (W : Lax342547.PairedWitnesses.Lists k n b degree r hr)
    (testers : Lax342547.ConcreteCut.Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) →
      Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) → Lax342547.ConcreteGeometry.Moment k n b degree)
    (holes : Lax342547.HoleRelation.HoleData
      (Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) → Frame (Lax342547.ConcreteGeometry.Coordinate k n b degree) H N M)
      (Lax342547.ConcreteCut.Profile k n b degree)
      (Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k) → Matrix N N Binary))
    (hrole : holes.a = testers.role) (hgradient : holes.T = Lax342547.ConcreteCut.gradient testers L R)
    (hU : ∀ o, holes.U o = (Lax342547.RawFrames.profileMap o).comp (Lax342547.ConcreteCut.Profile k n b degree).subtype)
    (hu : ∀ o, holes.u o = Lax342547.RawFrames.profileContraction o)
    (hkeys : ∀ x y, Lax342547.PairedWitnesses.MatchedKeys W (unitA x) (unitB y))
    (hroles : ∀ i z, testers.role (Lax342547.PairedWitnesses.leftWitness W i z) +
      testers.role (Lax342547.PairedWitnesses.rightWitness W i z) = 1)
    (hleft : ∀ i z x, fullContraction F (Lax342547.ConcreteCut.Profile k n b degree) i z x =
      (testers.role + Lax342547.ConcreteCut.gradient testers L R (Lax342547.PairedWitnesses.leftWitness W i z)) x)
    (hright : ∀ i z x, fullContraction F.flip (Lax342547.ConcreteCut.Profile k n b degree) z i x =
      (testers.role + Lax342547.ConcreteCut.gradient testers L R (Lax342547.PairedWitnesses.rightWitness W i z)) x)
    (hsmall : (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N) ≤
      1 / (2 : ℝ)^(16 * Fintype.card (Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k)) * Fintype.card H * Fintype.card (Lax342547.ConcreteGeometry.Coordinate k n b degree) + 1)) :
    1 / (2 : ℝ)^(16 * Fintype.card (Lax342547.CutProfiles.Component (Lax342547.TagGeometry.Tag k)) * Fintype.card H * Fintype.card (Lax342547.ConcreteGeometry.Coordinate k n b degree) + 1) ≤
      Lax342547.PairRecovery.pairMass α β (fun x y => ∀ i z,
        Lax342547.HoleRelation.Hole holes (unitA x i) (unitB y z)) := by
  classical
  have h := Lax342547.PrimalGramTests.primal_entry_agreement α β unitA unitB D E F hα hβ hαsum hβsum
    hD hE hcapA hcapB hsmall
  apply h.trans
  unfold Lax342547.FourierTests.patternMass Lax342547.PairRecovery.pairMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases he : entries (rawForms (unitA x) (unitB y)) = entries F
  · have hh := Lax342547.PrimalRecords.entries_give_four_holes W testers L R
      (unitA x) (unitB y) holes hrole hgradient hU hu (hkeys x y) hroles F he hleft hright
    simp only [if_pos he, if_pos hh]
    exact le_rfl
  · rw [if_neg he]
    split_ifs
    · exact mul_nonneg (hα x) (hβ y)
    · exact le_rfl

end Lax342547Proofs.PrimalGramTests
