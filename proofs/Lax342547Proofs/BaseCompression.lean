import Lax342547.BaseCompression
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Trace
import Lax342547Proofs.PrimalRetractions

namespace Lax342547Proofs.BaseCompression

set_option backward.isDefEq.respectTransparency false

open Lax342547.BaseCompression
open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.BaseCompression.fixing_observed_projection
---
-/
theorem fixing_observed_projection {V X : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary V]
    (U : Submodule Binary V) (L : V →ₗ[Binary] X) :
    ∃ p : V →ₗ[Binary] V, (∀ v ∈ U, p v = v) ∧ L.comp p = L ∧
      Module.finrank Binary (LinearMap.range p) ≤
        Module.finrank Binary U + Module.finrank Binary (LinearMap.range L) := by
  obtain ⟨s, hs⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let S := U ⊔ LinearMap.range s
  have hspan : S ⊔ LinearMap.ker L = ⊤ := by
    apply top_unique
    intro v _
    have hv : v - s (L.rangeRestrict v) ∈ LinearMap.ker L := by
      rw [LinearMap.mem_ker, map_sub]
      have he := congrArg Subtype.val (DFunLike.congr_fun hs (L.rangeRestrict v))
      change L (s (L.rangeRestrict v)) = L v at he
      rw [he, sub_self]
    have hr : s (L.rangeRestrict v) ∈ S := Submodule.mem_sup_right ⟨_, rfl⟩
    have hh := Submodule.add_mem (S ⊔ LinearMap.ker L)
      (Submodule.mem_sup_left hr) (Submodule.mem_sup_right hv)
    simpa using hh
  obtain ⟨p, hp, hfix, hker⟩ :=
    Lax342547Proofs.PrimalRetractions.preserving_retraction S (LinearMap.ker L) hspan
  refine ⟨p, fun v hv => hfix v (Submodule.mem_sup_left hv), ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    have hv : v ∈ S ⊔ LinearMap.ker L := by rw [hspan]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    simp [LinearMap.comp_apply, map_add, hfix u hu,
      (LinearMap.mem_ker.mp hw), (LinearMap.mem_ker.mp (hker w hw))]
  · have hr : LinearMap.range p ≤ S := by
      rintro _ ⟨v, rfl⟩
      exact hp v
    exact (Submodule.finrank_mono hr).trans
      ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans
        (Nat.add_le_add_left s.finrank_range_le _))

/--
---
conclusion: Lax342547.BaseCompression.liftBase_point
---
-/
theorem liftBase_point {Label Coord Base : Type}
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary))
    (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    liftBase (Coord := Coord) f (point p s z) = point p s (f z) := by
  ext ⟨a, c⟩
  cases c with
  | none => rfl
  | some b =>
    change f (fun b => p s a * z b) b = p s a * f z b
    exact congrFun (f.map_smul (p s a) z) b

/--
---
conclusion: Lax342547.BaseCompression.tensorMap_point
---
-/
theorem tensorMap_point {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary))
    (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    tensorMap (liftBase f) (pointMoment p s z) = pointMoment p s (f z) := by
  classical
  let : DecidableEq (Coord × Option Base) := Classical.decEq _
  simp only [tensorMap, LinearMap.comp_apply, mulRightLinearMap_apply, mulLeftLinearMap_apply]
  change LinearMap.toMatrix' (liftBase f) * pointMoment p s z *
    (LinearMap.toMatrix' (liftBase f)).transpose = _
  change LinearMap.toMatrix' (liftBase f) * Matrix.vecMulVec (point p s z) (point p s z) *
    (LinearMap.toMatrix' (liftBase f)).transpose = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  simp only [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, Lax342547.BaseCompression.liftBase_point]
  rfl

/--
---
conclusion: Lax342547.BaseCompression.tensorMap_moments
---
-/
theorem tensorMap_moments {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary)) (p : Label → Coord → Binary)
    (A : Set Base)
    (hA : ∀ z, (∀ b, b ∉ A → z b = 0) → ∀ b, b ∉ A → f z b = 0) :
    (momentSpace p A).map (tensorMap (liftBase f)) ≤ momentSpace p A := by
  rintro _ ⟨w, hw, rfl⟩
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, z, hz, rfl⟩ := hw
    rw [Lax342547.BaseCompression.tensorMap_point]
    exact Submodule.subset_span ⟨s, f z, hA z hz, rfl⟩
  | zero => simp
  | add u v _ _ hu hv => simpa using (momentSpace p A).add_mem hu hv
  | smul a w _ hw => simpa using (momentSpace p A).smul_mem a hw

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

/--
---
conclusion: Lax342547.BaseCompression.blockMap_allowed
---
-/
theorem blockMap_allowed {k n : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) (l : Tag k)
    (z : Base k n → Binary) (hz : ∀ q, q ∉ allowedBase k n l → z q = 0) :
    ∀ q, q ∉ allowedBase k n l → blockMap A z q = 0 := by
  intro q hq
  rcases q with ⟨⟨d, t⟩, i⟩ | ⟨q, i⟩
  · have hf : (fun j => z (Sum.inl ((d, t), j))) = 0 := by
      ext j
      exact hz _ hq
    change A (Sum.inl (d, t)) _ i = 0
    rw [hf, map_zero]
    rfl
  · exact False.elim (hq trivial)

/--
---
conclusion: Lax342547.BaseCompression.blockMap_tagSpace
---
-/
theorem blockMap_tagSpace {k n b degree : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) (l : Tag k) :
    (tagSpace k n b degree l).map (tensorMap (liftBase (blockMap A))) ≤ tagSpace k n b degree l :=
  Lax342547.BaseCompression.tensorMap_moments _ _ _ (Lax342547.BaseCompression.blockMap_allowed A l)

/--
---
conclusion: Lax342547.BaseCompression.componentMap_cut
---
-/
theorem componentMap_cut {Tag V : Type} [AddCommGroup V] [Module Binary V]
    (f : V →ₗ[Binary] V) (w : Tag → V) :
    componentMap (Tag := Tag) f (cutMap w) = cutMap (fun t => f (w t)) := by
  ext e
  exact map_sum f _ _

/--
---
conclusion: Lax342547.BaseCompression.blockMap_profile
---
-/
theorem blockMap_profile {k n b degree : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) :
    (Profile k n b degree).map (componentMap (tensorMap (liftBase (blockMap A)))) ≤
      Profile k n b degree := by
  rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
  let f := tensorMap (liftBase (Coord := SelectorCoordinates b degree) (blockMap A))
  have hw : ∀ t, f (w.val t) ∈ tagSpace k n b degree t := by
    intro t
    exact Lax342547.BaseCompression.blockMap_tagSpace A t ⟨w.val t, w.property t trivial, rfl⟩
  let v : Representation k n b degree := ⟨fun t => f (w.val t), by intro t _; exact hw t⟩
  refine ⟨v, ?_⟩
  exact (Lax342547.BaseCompression.componentMap_cut f w.val).symm

/--
---
conclusion: Lax342547.BaseCompression.liftBase_rank
---
-/
theorem liftBase_rank {Coord Base : Type} [Fintype Coord] [Fintype Base]
    (f : (Base → Binary) →ₗ[Binary] (Base → Binary)) :
    Module.finrank Binary (LinearMap.range (liftBase (Coord := Coord) f)) ≤
      Fintype.card Coord * (1 + Module.finrank Binary (LinearMap.range f)) := by
  let g : (Coord → Binary × LinearMap.range f) →ₗ[Binary] (Coord × Option Base → Binary) :=
    { toFun := fun w q => match q.2 with
        | none => (w q.1).1
        | some b => (w q.1).2.val b
      map_add' := by intro w v; ext ⟨a, q⟩; cases q <;> rfl
      map_smul' := by intro c w; ext ⟨a, q⟩; cases q <;> rfl }
  have hr : LinearMap.range (liftBase (Coord := Coord) f) ≤ LinearMap.range g := by
    rintro _ ⟨v, rfl⟩
    refine ⟨fun a => (v (a, none), f.rangeRestrict (fun b => v (a, some b))), ?_⟩
    ext ⟨a, q⟩
    cases q <;> rfl
  exact (Submodule.finrank_mono hr).trans (by
    simpa [Module.finrank_pi_fintype, Module.finrank_prod] using g.finrank_range_le)

/--
---
conclusion: Lax342547.BaseCompression.matrixPair_trace
---
-/
theorem matrixPair_trace {B : Type} [Fintype B] (M W : Matrix B B Binary) :
    Lax342547.ConcreteGeometry.matrixPair M W = Matrix.trace (M.transpose * W) := by
  classical
  simp only [Lax342547.ConcreteGeometry.matrixPair, LinearMap.sum_apply,
    LinearMap.smul_apply, matrixEntry, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/--
---
conclusion: Lax342547.BaseCompression.matrixPair_tensorMap
---
-/
theorem matrixPair_tensorMap {B : Type} [Fintype B]
    (f : (B → Binary) →ₗ[Binary] (B → Binary)) (M W : Matrix B B Binary) : by
      classical
      exact Lax342547.ConcreteGeometry.matrixPair M (tensorMap f W) =
        Lax342547.ConcreteGeometry.matrixPair
          ((LinearMap.toMatrix' f).transpose * M * LinearMap.toMatrix' f) W := by
  classical
  simp only [tensorMap, LinearMap.comp_apply, mulRightLinearMap_apply, mulLeftLinearMap_apply,
    Lax342547.BaseCompression.matrixPair_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/--
---
conclusion: Lax342547.BaseCompression.tensorMap_target
---
-/
theorem tensorMap_target {B : Type} [Fintype B]
    (f : (B → Binary) →ₗ[Binary] (B → Binary)) (M : Matrix B B Binary)
    (hM : by classical exact (LinearMap.toMatrix' f).transpose * M * LinearMap.toMatrix' f = M) :
    (Lax342547.ConcreteGeometry.matrixPair M).comp (tensorMap f) =
      Lax342547.ConcreteGeometry.matrixPair M := by
  apply LinearMap.ext
  intro W
  exact (Lax342547.BaseCompression.matrixPair_tensorMap f M W).trans (congrArg (fun M => Lax342547.ConcreteGeometry.matrixPair M W) hM)

/--
---
conclusion: Lax342547.BaseCompression.blockMap_rank
---
-/
theorem blockMap_rank {k n : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) :
    Module.finrank Binary (LinearMap.range (blockMap A)) ≤
      ∑ q, Module.finrank Binary (LinearMap.range (A q)) := by
  let g : (∀ q, LinearMap.range (A q)) →ₗ[Binary] (Base k n → Binary) :=
    { toFun := fun w q => match q with
        | Sum.inl ((d, t), i) => (w (Sum.inl (d, t))).val i
        | Sum.inr (q, i) => (w (Sum.inr q)).val i
      map_add' := by intro w v; ext q; rcases q with ⟨⟨d, t⟩, i⟩ | ⟨q, i⟩ <;> rfl
      map_smul' := by intro c w; ext q; rcases q with ⟨⟨d, t⟩, i⟩ | ⟨q, i⟩ <;> rfl }
  have hr : LinearMap.range (blockMap A) ≤ LinearMap.range g := by
    rintro _ ⟨v, rfl⟩
    let w : ∀ q, LinearMap.range (A q) := fun q => match q with
      | Sum.inl (d, t) => (A (Sum.inl (d, t))).rangeRestrict (fun j => v (Sum.inl ((d, t), j)))
      | Sum.inr q => (A (Sum.inr q)).rangeRestrict (fun j => v (Sum.inr (q, j)))
    refine ⟨w, ?_⟩
    ext q
    rcases q with ⟨⟨d, t⟩, i⟩ | ⟨q, i⟩ <;> rfl
  exact (Submodule.finrank_mono hr).trans (by
    simpa only [Module.finrank_pi_fintype] using g.finrank_range_le)

/--
---
conclusion: Lax342547.BaseCompression.concrete_compression_rank
---
-/
theorem concrete_compression_rank {k n b degree D : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary))
    (hA : ∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤ D) :
    Module.finrank Binary (LinearMap.range
      (liftBase (Coord := SelectorCoordinates b degree) (blockMap A))) ≤
      Fintype.card (SelectorCoordinates b degree) * (1 + ((2 * k + 1)^2 + 3) * D) := by
  have hb := (Lax342547.BaseCompression.blockMap_rank A).trans (Finset.sum_le_sum (fun q _ => hA q))
  have hh : Module.finrank Binary (LinearMap.range (blockMap A)) ≤ ((2 * k + 1)^2 + 3) * D := by
    simpa [Block, Tag, Fintype.card_sum, Fintype.card_prod, ZMod.card, pow_two] using hb
  exact (Lax342547.BaseCompression.liftBase_rank (blockMap A)).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hh 1))

end Lax342547Proofs.BaseCompression
