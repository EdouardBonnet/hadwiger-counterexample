import Lax342547.UnaryMixer
import Lax342547Proofs.FormalQuadratic
import Lax342547Proofs.RestrictionRank
import Lax342547Proofs.Atoms
import Lax342547Proofs.AtomDirections
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.UnaryMixer

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.UnaryMixer

variable {E I : Type} [Fintype E] [Fintype I]

omit [Fintype E] in
theorem middle_nondegenerate {r : E → ℕ}
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hH : ∀ e, Function.Injective (H e).mulVec) {inc : Finset E} {J : ℕ}
    (t : Block inc J) : (middle H t).Nondegenerate := by
  have h (e : E) : (H e).toBilin'.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
    apply Matrix.separatingRight_toBilin'_iff.mpr
    rw [Matrix.separatingRight_iff_forall_mulVec_eq_zero]
    intro v hv
    apply hH e
    simpa using hv
  cases t with
  | inl p => exact h p.2.1
  | inr p => exact h p.2.2

theorem rows_dimension (r : E → ℕ) (inc : Finset E) (J : ℕ) :
    Module.finrank Binary (Rows r inc J) = 4 * J * inc.card * ∑ e, r e := by
  classical
  simp only [Rows, Lax342547.FormalQuadratic.Rows, Module.finrank_pi_fintype,
    Module.finrank_prod,
    Fintype.sum_sum_type, Fintype.sum_prod_type, blockRank]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    Module.finrank_self, mul_one, Nat.cast_id]
  ring

/--
---
conclusion: Lax342547.UnaryMixer.formal_rank
---
Every formal block has a nonsingular middle matrix. Their polar maps
are jointly injective. Counting the two row halves, the two orders,
the J mixer copies, and the incident components gives the exact rank.
-/
theorem formal_rank {r : E → ℕ} (inc : Finset E) (J : ℕ)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hH : ∀ e, Function.Injective (H e).mulVec) :
    Module.finrank Binary (LinearMap.range (formalQuadratic inc J H).polarBilin) =
      4 * J * inc.card * ∑ e, r e := by
  unfold formalQuadratic
  rw [LinearMap.finrank_range_of_inj (FormalQuadratic.polar_injective (middle (inc := inc) (J := J) H)
    (middle_nondegenerate H hH))]
  exact rows_dimension r inc J

/--
---
conclusion: Lax342547.UnaryMixer.substitution_rank
---
Substituting a row map whose image has codimension at most s loses
at most 2s from the exact formal polar rank.
-/
theorem substitution_rank {r : E → ℕ} (inc : Finset E) (J : ℕ)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hH : ∀ e, Function.Injective (H e).mulVec)
    {U : Type} [AddCommGroup U] [Module Binary U]
    (A : U →ₗ[Binary] Rows r inc J) (s : ℕ)
    (hA : Module.finrank Binary (Rows r inc J) ≤
      Module.finrank Binary (LinearMap.range A) + s) :
    4 * J * inc.card * ∑ e, r e ≤
      Module.finrank Binary (LinearMap.range (LinearMap.compl₁₂
        (formalQuadratic inc J H).polarBilin A A)) + 2 * s := by
  have h := RestrictionRank.bilinear_pullback_rank (formalQuadratic inc J H).polarBilin A
  change Module.finrank Binary (LinearMap.range (formalQuadratic inc J H).polarBilin) ≤
    Module.finrank Binary (LinearMap.range (LinearMap.compl₁₂
      (formalQuadratic inc J H).polarBilin A A)) +
      2 * (Module.finrank Binary (Rows r inc J) - Module.finrank Binary (LinearMap.range A)) at h
  rw [formal_rank inc J H hH] at h
  omega

open Lax342547.ConcreteGeometry

variable [DecidableEq I]

theorem matrixPair_vecMulVec (X : Matrix I I Binary) (u v : I → Binary) :
    matrixPair X (Matrix.vecMulVec u v) = X.toBilin' u v := by
  classical
  simp only [matrixPair, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    matrixEntry, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] in
theorem matrixPair_comm (X Y : Matrix I I Binary) : matrixPair X Y = matrixPair Y X := by
  simp [matrixPair, matrixEntry, LinearMap.sum_apply, mul_comm]

theorem factor_bilin {d : ℕ} (Z : Matrix I (Fin d) Binary)
    (H : Matrix (Fin d) (Fin d) Binary) (u v : I → Binary) :
    (Z * H * Z.transpose).toBilin' u v = H.toBilin' (Z.transpose.mulVec u) (Z.transpose.mulVec v) := by
  classical
  have h := congrArg (fun B : LinearMap.BilinForm Binary (I → Binary) => B u v)
    (H.toBilin'_comp Z.transpose Z.transpose)
  simpa only [Matrix.transpose_transpose, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using h.symm

theorem forward_product {d : ℕ} (Z : Matrix I (Fin d) Binary)
    (H : Matrix (Fin d) (Fin d) Binary) (L R : Matrix I I Binary) (v : I → Binary) :
    matrixPair (Z * H * Z.transpose) (L * Matrix.vecMulVec v v * R.transpose) =
      H.toBilin' ((Z.transpose * L).mulVec v) ((Z.transpose * R).mulVec v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, matrixPair_vecMulVec,
    factor_bilin, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem reverse_product {d : ℕ} (Z : Matrix I (Fin d) Binary)
    (H : Matrix (Fin d) (Fin d) Binary) (L R : Matrix I I Binary) (v : I → Binary) :
    matrixPair (Matrix.vecMulVec v v) (L * (Z * H * Z.transpose) * R.transpose) =
      H.toBilin' ((L * Z).transpose.mulVec v) ((R * Z).transpose.mulVec v) := by
  classical
  rw [matrixPair_comm, matrixPair_vecMulVec]
  have h := congrArg (fun B : LinearMap.BilinForm Binary (I → Binary) => B v v)
    (H.toBilin'_comp (L * Z).transpose (R * Z).transpose)
  simpa only [Matrix.transpose_transpose, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
    Matrix.transpose_mul, Matrix.mul_assoc] using h.symm

theorem quadratic_expansion {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (L R : Fin J → E → E → Matrix I I Binary) (v : I → Binary) :
    formalQuadratic inc J H (rowMap inc Z L R v) =
      (∑ j, ∑ e, ∑ f : {f : E // f ∈ inc},
        matrixPair (Z e * H e * (Z e).transpose)
          (L j e f.val * Matrix.vecMulVec v v * (R j e f.val).transpose)) +
      ∑ j, ∑ e : {e : E // e ∈ inc}, ∑ f,
        matrixPair (Matrix.vecMulVec v v)
          (L j e.val f * (Z f * H f * (Z f).transpose) * (R j e.val f).transpose) := by
  classical
  simp only [formalQuadratic, FormalQuadratic.quadratic_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, middle, rowMap, LinearMap.pi_apply, forward_product, reverse_product]
  rfl

open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms

/--
---
conclusion: Lax342547.UnaryMixer.incident_card
---
Pairing l with another tag is a bijection from the tags different
from l to the two-element components incident to l.
-/
theorem incident_card {k : ℕ} (l : Tag k) : (incident l).card = 2 * k := by
  classical
  let f : {t : Tag k // t ≠ l} → {e : Component (Tag k) // e ∈ incident l} :=
    fun t => ⟨⟨{l, t.val}, Finset.card_pair t.property.symm⟩, by simp [incident]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      apply Subtype.ext
      have hs : ({l, u.val} : Finset (Tag k)) = {l, v.val} :=
        congrArg (fun e : {e : Component (Tag k) // e ∈ incident l} => e.val.val) h
      have hu : u.val ∈ ({l, v.val} : Finset (Tag k)) := by rw [← hs]; simp
      simpa [u.property] using hu
    · intro e
      obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.val.property
      have hmem : l ∈ e.val.val := (Finset.mem_filter.mp e.property).2
      have hl : l = a ∨ l = b := by simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hmem
      rcases hl with rfl | rfl
      · refine ⟨⟨b, hab.symm⟩, ?_⟩
        apply Subtype.ext
        exact Subtype.ext he.symm
      · refine ⟨⟨a, hab⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change ({l, a} : Finset (Tag k)) = e.val.val
        rw [he, Finset.pair_comm]
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_subtype_compl (fun t : Tag k => t = l), Fintype.card_subtype_eq] at hc
  simpa [Tag, ZMod.card] using hc.symm

/--
---
conclusion: Lax342547.UnaryMixer.mixer_atom_expansion
---
Expand the atom's incident components in the two orders of the mixer
sum. The symmetric component factorization turns each forward or
reverse contribution into precisely its indexed formal product.
-/
theorem mixer_atom_expansion {k n b degree J : ℕ}
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) :
    mixingForm L R x (atom l s z hz) + mixingForm L R (atom l s z hz) x =
      formalQuadratic (incident l) J H (rowMap (incident l) Z L R (point selectorEval s z)) := by
  classical
  rw [quadratic_expansion, ConcreteCut.mixingForm_apply, ConcreteCut.mixingForm_apply]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_subtype (F := Finset.Subtype.fintype (incident l))
      (incident l) (fun _ => Iff.rfl) (fun f =>
        matrixPair (Z e * H e * (Z e).transpose)
          (L j e f * Matrix.vecMulVec (point selectorEval s z) (point selectorEval s z) *
            (R j e f).transpose)), ← Fintype.sum_ite_mem (incident l)]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : l ∈ f.val
    · simp only [Atoms.atom_component, hf, if_pos]
      simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and, hf, if_pos, hfactor]
      rfl
    · simp [Atoms.atom_component, hf, incident]
  · apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_subtype (F := Finset.Subtype.fintype (incident l))
      (incident l) (fun _ => Iff.rfl) (fun e => ∑ f,
        matrixPair (Matrix.vecMulVec (point selectorEval s z) (point selectorEval s z))
          (L j e f * (Z f * H f * (Z f).transpose) * (R j e f).transpose)),
      ← Fintype.sum_ite_mem (incident l)]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : l ∈ e.val
    · simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and, he, if_pos]
      apply Finset.sum_congr rfl
      intro f _
      simp only [Atoms.atom_component, he, if_pos, hfactor]
      rfl
    · simp [Atoms.atom_component, he, incident, matrixPair, matrixEntry]

theorem atomAlongZ_aTag {k n b degree r₀ : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (v : Fin n → Binary) (t : Tag k) :
    D.aTag t (atomAlongZ l s z hz v) = D.aTag t (atom l s z hz) := by
  simp [atomAlongZ, Atoms.atom_aTag, ConcreteGeometry.blockTester_point,
    Lax342547.AtomDirections.varyBlock, free, ordinary]

theorem atomAlongZ_bTag {k n b degree r₀ : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (v : Fin n → Binary) (t : Tag k) :
    D.bTag t (atomAlongZ l s z hz v) = D.bTag t (atom l s z hz) := by
  simp [atomAlongZ, Atoms.atom_bTag, ConcreteGeometry.blockTester_point,
    Lax342547.AtomDirections.varyBlock, free, shared]

theorem atomAlongZ_role {k n b degree r₀ : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (v : Fin n → Binary) :
    D.role (atomAlongZ l s z hz v) = D.role (atom l s z hz) := by
  simp only [Testers.role, LinearMap.sum_apply, atomAlongZ_aTag]

theorem testerTerm_atomAlongZ {k n b degree r₀ : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (x : Profile k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (v : Fin n → Binary) :
    testerTerm D x (atomAlongZ l s z hz v) = testerTerm D x (atom l s z hz) := by
  simp [testerTerm, Lax342547.GradientForm.form, GradientForm.rankOne_apply,
    LinearMap.sum_apply, atomAlongZ_role, atomAlongZ_aTag, atomAlongZ_bTag]

theorem gradient_eq {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : Profile k n b degree) :
    gradient D L R x y = testerTerm D x y + (mixingForm L R x y + mixingForm L R y x) := by
  simp [gradient, testerTerm, Lax342547.GradientForm.form, add_assoc]

/--
---
conclusion: Lax342547.UnaryMixer.unary_affine_quadratic
---
The tester term is constant along the free Z block. The point input
changes affinely by its direction matrix, and the indexed row map is
linear. Combining these facts with the concrete mixer expansion gives
the claimed affine substitution with an explicitly fixed linear part.
-/
theorem unary_affine_quadratic {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (v : Fin n → Binary) :
    gradient D L R x (atomAlongZ l s z hz v) =
      testerTerm D x (atom l s z hz) + formalQuadratic (incident l) J H
        (rowMap (incident l) Z L R (point selectorEval s z) + zRows Z L R l s v) := by
  rw [gradient_eq, testerTerm_atomAlongZ]
  congr 1
  unfold atomAlongZ
  rw [mixer_atom_expansion x Z H hfactor, AtomDirections.point_varyBlock, map_add]
  rfl

/--
---
conclusion: Lax342547.UnaryMixer.unary_polar
---
Apply the four-term binary polar operator to the actual atom test.
Its affine expansion cancels both the constant tester value and the
non-Z shift, leaving exactly the formal polar form pulled back along
the fixed Z row map.
-/
theorem unary_polar {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (u v : Fin n → Binary) :
    Lax342547.FormalQuadratic.affinePolar (fun w => gradient D L R x (atomAlongZ l s z hz w)) u v =
      (formalQuadratic (incident l) J H).polarBilin (zRows Z L R l s u) (zRows Z L R l s v) := by
  simp_rw [unary_affine_quadratic D x Z H hfactor L R l s z hz]
  change Lax342547.FormalQuadratic.affinePolar (fun w => testerTerm D x (atom l s z hz) +
    Lax342547.FormalQuadratic.cross (middle H)
      (rowMap (incident l) Z L R (point selectorEval s z) + zRows Z L R l s w)
      (rowMap (incident l) Z L R (point selectorEval s z) + zRows Z L R l s w)) u v = _
  rw [FormalQuadratic.affine_polar]
  rw [formalQuadratic, Lax342547.FormalQuadratic.quadratic,
    LinearMap.BilinMap.polarBilin_toQuadraticMap]
  rfl

/--
---
conclusion: Lax342547.UnaryMixer.unary_rank_bound
---
The actual atom test has the polar matrix of the affine formal
quadratic. Its rank is the rank of the pulled-back polar map, so the
formal substitution estimate applies directly to the actual Z bits.
-/
theorem unary_rank_bound {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (hH : ∀ e, Function.Injective (H e).mulVec)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (s₀ : ℕ)
    (hA : Module.finrank Binary (Rows r (incident l) J) ≤
      Module.finrank Binary (LinearMap.range (zRows Z L R l s)) + s₀) :
    4 * J * (incident l).card * ∑ e, r e ≤
      (Lax342547.FormalQuadratic.polarMatrix
        (fun w => gradient D L R x (atomAlongZ l s z hz w))).rank + 2 * s₀ := by
  simp_rw [unary_affine_quadratic D x Z H hfactor L R l s z hz]
  change 4 * J * (incident l).card * ∑ e, r e ≤
    (Lax342547.FormalQuadratic.polarMatrix (fun w => testerTerm D x (atom l s z hz) +
      Lax342547.FormalQuadratic.cross (middle H)
        (rowMap (incident l) Z L R (point selectorEval s z) + zRows Z L R l s w)
        (rowMap (incident l) Z L R (point selectorEval s z) + zRows Z L R l s w))).rank + 2 * s₀
  rw [FormalQuadratic.affine_polar_matrix_rank]
  have h := substitution_rank (incident l) J H hH (zRows Z L R l s) s₀ hA
  have hpolar : (formalQuadratic (incident l) J H).polarBilin =
      Lax342547.FormalQuadratic.cross (middle H) +
        (Lax342547.FormalQuadratic.cross (middle H)).flip :=
    LinearMap.BilinMap.polarBilin_toQuadraticMap
  rw [hpolar] at h
  exact h

theorem total_rank_pos_of_factor_nonzero {k n b degree : ℕ}
    (x : Profile k n b degree) (hx : x ≠ 0) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e) : 0 < ∑ e, r e := by
  classical
  by_contra hn
  have hr (e : Component (Tag k)) : r e = 0 := by
    have hle := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Component (Tag k)))) =>
      Nat.zero_le (r i)) (Finset.mem_univ e)
    omega
  apply hx
  apply Subtype.ext
  funext e
  change x.val e = 0
  rw [← hfactor e]
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  have ha := a.isLt
  have hr0 := hr e
  omega

/--
---
conclusion: Lax342547.UnaryMixer.unary_rank_lower
---
A nonzero profile has positive total factor rank, and a positive k
gives incident components at every tag. The exact formal rank is at
least 2J. Losing at most twice the Z row codimension proves the unary
lower bound, uniformly over the fixed non-Z values.
-/
theorem unary_rank_lower {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n} (hk : 0 < k)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) (hx : x ≠ 0) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (hH : ∀ e, Function.Injective (H e).mulVec)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (s₀ : ℕ)
    (hA : Module.finrank Binary (Rows r (incident l) J) ≤
      Module.finrank Binary (LinearMap.range (zRows Z L R l s)) + s₀) :
    2 * (J - s₀) ≤
      (Lax342547.FormalQuadratic.polarMatrix
        (fun w => gradient D L R x (atomAlongZ l s z hz w))).rank := by
  have hrpos := total_rank_pos_of_factor_nonzero x hx Z H hfactor
  have hinc : 0 < (incident l).card := by rw [incident_card]; omega
  have hm : 1 ≤ (incident l).card * ∑ e, r e := Nat.mul_pos hinc hrpos
  have hlower : 2 * J ≤ 4 * J * (incident l).card * ∑ e, r e := calc
    _ ≤ 4 * J := by omega
    _ = 4 * J * 1 := by simp
    _ ≤ 4 * J * ((incident l).card * ∑ e, r e) := Nat.mul_le_mul_left _ hm
    _ = _ := by ring
  have h := unary_rank_bound D x Z H hfactor hH L R l s z hz s₀ hA
  omega

/--
---
conclusion: Lax342547.UnaryMixer.row_space_dimension
---
The row space is the image of the dual row map. Its dimension is at
most the formal row dimension, which is 4J(2k) times the total factor
rank. This bound is independent of n.
-/
theorem row_space_dimension {k n b degree J K : ℕ} {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (hrank : ∑ e, r e ≤ K) :
    Module.finrank Binary (zRowSpace Z L R l s) ≤ 4 * J * (2 * k) * K := by
  have h := (zRows Z L R l s).dualMap.finrank_range_add_finrank_ker
  rw [Subspace.dual_finrank_eq, rows_dimension, incident_card] at h
  change Module.finrank Binary (LinearMap.range (zRows Z L R l s).dualMap) ≤ _
  exact (Nat.le.intro h).trans (Nat.mul_le_mul_left _ hrank)

/--
---
conclusion: Lax342547.UnaryMixer.unary_depends_on_rows
---
Equality on the fixed row space means every functional on the formal
row vectors has the same value. The dual separates points, so the row
vectors agree. Their affine quadratic evaluations therefore agree.
-/
theorem unary_depends_on_rows {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (u v : Fin n → Binary)
    (hrows : ∀ a ∈ zRowSpace Z L R l s, a u = a v) :
    gradient D L R x (atomAlongZ l s z hz u) = gradient D L R x (atomAlongZ l s z hz v) := by
  have heq : zRows Z L R l s u = zRows Z L R l s v := by
    apply Module.eval_apply_injective Binary
    apply LinearMap.ext
    intro a
    exact hrows ((zRows Z L R l s).dualMap a) ⟨a, rfl⟩
  rw [unary_affine_quadratic D x Z H hfactor, unary_affine_quadratic D x Z H hfactor, heq]

end Lax342547Proofs.UnaryMixer
