import Lax342547.ComponentTests
import Lax342547.PrimalRecords
import Lax342547.PairedFrames
import Lax342547.PairRecovery

/-!
---
title: Actual primal-channel scalar tests and retained-cell four-hole probability
type: lemma
---
The two nominal orientations of every raw component realize the actual cross forms. The paper primal-channel entry records are linear Gram tests, and their joint Fourier agreement implies all four actual holes under the constructed target gradients.
-/

namespace Lax342547.PrimalGramTests

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TableSpaces
open Lax342547.TableContractions Lax342547.RawContractions Lax342547.ReferencePins
open Lax342547.ProductImages Lax342547.RetainedCharacters Lax342547.CoefficientPhase
open Lax342547.ComponentTests Lax342547.PrimalRecords Lax342547.RawFrames

noncomputable def orientedForms {Comp B H : Type} (F : CrossForms Comp B H)
    (a : Comp × Bool) : LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary) :=
  if a.2 then F.forward a.1 else (F.reverse a.1).flip

noncomputable def leftMatrices {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary := observationMatrix o a

noncomputable def rightMatrices {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary := observationMatrix o (a.1,!a.2)

axiom gram_form_evaluation {I N : Type} [Fintype I] [Fintype N]
    (X Y : Matrix N I Binary) (u v : I → Binary) :
    actualForm X Y u v = dotProduct (X.mulVec u) (Y.mulVec v)

axiom raw_oriented_forms {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (oA oB : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) :
    actualForm (leftMatrices oA a) (rightMatrices oB a) = orientedForms (rawForms oA oB) a

axiom matrix_pair_outer {I : Type} [Fintype I]
    (T : LinearMap.BilinForm Binary (I → Binary)) (u v : I → Binary) : by
      classical
      exact matrixPair (LinearMap.BilinForm.toMatrix' T) (Matrix.vecMulVec u v) = T u v

noncomputable def entryAxis {Comp B H : Type} (t : EntryIndex Comp B H) : Comp × Bool :=
  (t.2.2.1, decide ((t.1 = 0) ↔ (t.2.1 = 0)))

noncomputable def entryLeft {Comp B H : Type} (t : EntryIndex Comp B H) : (Fin 2 × (B ⊕ H)) → Binary := by
  classical
  exact if t.1 = 0 then primalEmbedding t.2.2.2.1 (Pi.single t.2.2.2.2.2.1 1)
    else channelEmbedding t.2.2.2.2.1 (Pi.single t.2.2.2.2.2.2 1)

noncomputable def entryRight {Comp B H : Type} (t : EntryIndex Comp B H) : (Fin 2 × (B ⊕ H)) → Binary := by
  classical
  exact if t.1 = 0 then channelEmbedding t.2.2.2.2.1 (Pi.single t.2.2.2.2.2.2 1)
    else primalEmbedding t.2.2.2.1 (Pi.single t.2.2.2.2.2.1 1)

noncomputable def entryTests {Comp B H : Type} (t : EntryIndex Comp B H)
    (a : Comp × Bool) : Matrix (Fin 2 × (B ⊕ H)) (Fin 2 × (B ⊕ H)) Binary := by
  classical
  exact if a = entryAxis t then Matrix.vecMulVec (entryLeft t) (entryRight t) else 0

axiom entry_target_bits {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) : targetBits entryTests (orientedForms F) = entries F

axiom entry_actual_bits {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (oA oB : Fin 2 → Comp → Frame B H N E) :
    actualBits entryTests (leftMatrices oA) (rightMatrices oB) = entries (rawForms oA oB)

axiom primal_entry_agreement {ΩA ΩB Comp B H N : Type}
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
        (fun ab => entries (rawForms (unitA ab.1) (unitB ab.2))) (entries F)

axiom primal_cell_four_holes {ΩA ΩB H N : Type} {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
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
        Lax342547.HoleRelation.Hole holes (unitA x i) (unitB y z))

end Lax342547.PrimalGramTests
