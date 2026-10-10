import Lax342547.ResponseSolvability
import Lax342547Proofs.EffectiveObstructions
import Lax342547Proofs.RecipeResiduals

namespace Lax342547Proofs.ResponseSolvability

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PairedAnnihilators Lax342547.BarredSpaces
open Lax342547.ChannelChanges Lax342547.TableContractions Lax342547.DerivativeResponses
open Lax342547.TableSpaces Lax342547.ResponseSolvability

set_option backward.isDefEq.respectTransparency false

theorem matrixPair_add {B : Type} [Fintype B] (A C : Matrix B B Binary) :
    matrixPair (A + C) = matrixPair A + matrixPair C := by
  classical
  simp [matrixPair, add_smul, Finset.sum_add_distrib]

theorem matrixPair_smul {B : Type} [Fintype B] (a : Binary) (A : Matrix B B Binary) :
    matrixPair (a • A) = a • matrixPair A := by
  classical
  simp [matrixPair, smul_smul, Finset.smul_sum]

theorem ambient_add_left {B H : Type} [Fintype B] [Fintype H]
    (f f' g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient (f + f') g =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient f' g := by
  classical
  unfold Lax342547.TensorContractions.ambient
  rw [← matrixPair_add]
  congr 1
  ext i j
  simp [LinearMap.BilinForm.toMatrix'_apply]

theorem ambient_add_right {B H : Type} [Fintype B] [Fintype H]
    (f g g' : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient f (g + g') =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient f g' := by
  classical
  unfold Lax342547.TensorContractions.ambient
  rw [← matrixPair_add]
  congr 1
  ext i j
  simp [LinearMap.BilinForm.toMatrix'_apply, dotProduct_add]

theorem ambient_smul_left {B H : Type} [Fintype B] [Fintype H]
    (a : Binary) (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient (a • f) g =
      a • Lax342547.TensorContractions.ambient f g := by
  classical
  unfold Lax342547.TensorContractions.ambient
  rw [← matrixPair_smul]
  congr 1
  ext i j
  simp [LinearMap.BilinForm.toMatrix'_apply]

theorem ambient_smul_right {B H : Type} [Fintype B] [Fintype H]
    (a : Binary) (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient f (a • g) =
      a • Lax342547.TensorContractions.ambient f g := by
  classical
  unfold Lax342547.TensorContractions.ambient
  rw [← matrixPair_smul]
  congr 1
  ext i j
  simp [LinearMap.BilinForm.toMatrix'_apply]

theorem pure_add {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H))
    (β β' : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary) :
    pureResponse D E (β + β') = pureResponse D E β + pureResponse D E β' := by
  classical
  unfold pureResponse
  have ht : ∀ i : Fin 2,
      LinearMap.BilinForm.toMatrix' ((β + β').compl₁₂
          (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i))) =
        LinearMap.BilinForm.toMatrix' (β.compl₁₂
          (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i))) +
        LinearMap.BilinForm.toMatrix' (β'.compl₁₂
          (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i))) := by
    intro i
    ext a b
    simp [LinearMap.BilinForm.toMatrix'_apply]
  simp [ht, matrixPair_add, LinearMap.add_comp, Finset.sum_add_distrib]

theorem pure_smul {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (a : Binary)
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary) :
    pureResponse D E (a • β) = a • pureResponse D E β := by
  classical
  unfold pureResponse
  have ht : ∀ i : Fin 2,
      LinearMap.BilinForm.toMatrix' ((a • β).compl₁₂
          (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i))) =
        a • LinearMap.BilinForm.toMatrix' (β.compl₁₂
          (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i))) := by
    intro i
    ext b c
    simp [LinearMap.BilinForm.toMatrix'_apply]
  simp [ht, matrixPair_smul, LinearMap.smul_comp]

theorem restriction_add {B H : Type} [Fintype H] (D : Submodule Binary (Nominal B H))
    (S : Submodule Binary (H → Binary))
    (δ δ' : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    restriction D S (δ + δ') i = restriction D S δ i + restriction D S δ' i := by
  ext v h
  simp [restriction]

theorem restriction_smul {B H : Type} [Fintype H] (D : Submodule Binary (Nominal B H))
    (S : Submodule Binary (H → Binary)) (a : Binary)
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    restriction D S (a • δ) i = a • restriction D S δ i := by
  ext v h
  simp [restriction]

theorem component_add {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ δ' : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε ε' : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    componentResponse F e z D E S T (δ + δ') (ε + ε') =
      componentResponse F e z D E S T δ ε + componentResponse F e z D E S T δ' ε' := by
  classical
  simp only [componentResponse, restriction_add, ambient_add_left, ambient_add_right]
  simp only [add_add_add_comm, LinearMap.add_comp, Finset.sum_add_distrib]

theorem component_smul {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (a : Binary) (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    componentResponse F e z D E S T (a • δ) (a • ε) =
      a • componentResponse F e z D E S T δ ε := by
  classical
  simp only [componentResponse, restriction_smul, ambient_smul_left, ambient_smul_right,
    ← smul_add, LinearMap.smul_comp, ← Finset.smul_sum]

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

omit [Fintype H] in
theorem pure_family_add (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (β β' : Lax342547.PureObstructions.Parameters W P U V) :
    Lax342547.PureObstructions.response W P U V (β + β') =
      Lax342547.PureObstructions.response W P U V β + Lax342547.PureObstructions.response W P U V β' := by
  classical
  simp [Lax342547.PureObstructions.response, Pi.add_apply, pure_add,
    LinearMap.add_comp, Finset.sum_add_distrib]

omit [Fintype H] in
theorem pure_family_smul (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (a : Binary) (β : Lax342547.PureObstructions.Parameters W P U V) :
    Lax342547.PureObstructions.response W P U V (a • β) =
      a • Lax342547.PureObstructions.response W P U V β := by
  classical
  simp [Lax342547.PureObstructions.response, Pi.smul_apply, pure_smul,
    LinearMap.smul_comp, Finset.smul_sum]

theorem derivative_add (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δ δ' : PlusParameters W P Q U z) (ε ε' : MinusParameters W P Q V z) :
    response W P Q U V F z (δ + δ') (ε + ε') =
      response W P Q U V F z δ ε + response W P Q U V F z δ' ε' := by
  classical
  simp [response, Pi.add_apply, component_add, LinearMap.add_comp, Finset.sum_add_distrib]

theorem derivative_smul (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (a : Binary) (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    response W P Q U V F z (a • δ) (a • ε) = a • response W P Q U V F z δ ε := by
  classical
  simp [response, Pi.smul_apply, component_smul, LinearMap.smul_comp, Finset.smul_sum]

/--
---
conclusion: Lax342547.ResponseSolvability.full_add
---
The pure quotient family and both allowed derivative families are additive in their parameters. Coordinate matrix pairing and both channel contractions are additive in the appropriate argument.
-/
theorem full_add (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (β β' : Lax342547.PureObstructions.Parameters W P U V)
    (δ δ' : PlusParameters W P Q U z) (ε ε' : MinusParameters W P Q V z) :
    fullResponse W P Q U V F z (β + β') (δ + δ') (ε + ε') =
      fullResponse W P Q U V F z β δ ε + fullResponse W P Q U V F z β' δ' ε' := by
  rw [fullResponse, pure_family_add, derivative_add]
  simp only [fullResponse]
  abel

/--
---
conclusion: Lax342547.ResponseSolvability.full_smul
---
Scalar multiplication of all three parameter families scales the full response. This proves homogeneity on the actual pair of cut profiles.
-/
theorem full_smul (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (a : Binary) (β : Lax342547.PureObstructions.Parameters W P U V)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    fullResponse W P Q U V F z (a • β) (a • δ) (a • ε) =
      a • fullResponse W P Q U V F z β δ ε := by
  rw [fullResponse, pure_family_smul, derivative_smul, ← smul_add]
  rfl

noncomputable def parameterMap (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2) :
    Parameters W P Q U V z →ₗ[Binary] Module.Dual Binary (Fin 2 → Profile k n b degree) where
  toFun p := fullResponse W P Q U V F z p.1 p.2.1 p.2.2
  map_add' p q := full_add W P Q U V F z p.1 q.1 p.2.1 q.2.1 p.2.2 q.2.2
  map_smul' a p := full_smul W P Q U V F z a p.1 p.2.1 p.2.2

/--
---
conclusion: Lax342547.ResponseSolvability.dual_range
---
The finite-dimensional double-annihilator theorem identifies the response range with every target functional vanishing on its coannihilator. Membership in the actual range supplies parameters.
-/
theorem dual_range {K A X : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (R : A →ₗ[K] Module.Dual K X) (t : Module.Dual K X)
    (h : ∀ x, (∀ a, R a x = 0) → t x = 0) : ∃ a, R a = t := by
  apply LinearMap.mem_range.mp
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range R)]
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro x hx
  apply h x
  intro a
  exact (Submodule.mem_dualCoannihilator _).mp hx _ (LinearMap.mem_range_self R a)

/--
---
conclusion: Lax342547.ResponseSolvability.solvable_of_annihilator_zero
---
Package the pure and derivative families into a product module and prove their response map linear using the checked additivity and homogeneity. Apply double annihilation to its actual range.
-/
theorem solvable_of_annihilator_zero (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (t : Module.Dual Binary (Fin 2 → Profile k n b degree))
    (h : ∀ x, Annihilates W P Q U V F z x → t x = 0) :
    ∃ β δ ε, fullResponse W P Q U V F z β δ ε = t := by
  have hzero : ∀ x, (∀ p : Parameters W P Q U V z,
      parameterMap W P Q U V F z p x = 0) → t x = 0 := by
    intro x hx
    apply h x
    intro β δ ε
    exact hx (β, δ, ε)
  obtain ⟨p, hp⟩ := dual_range (A := Parameters W P Q U V z)
    (X := Fin 2 → Profile k n b degree) (parameterMap W P Q U V F z) t hzero
  exact ⟨p.1, p.2.1, p.2.2, hp⟩

open Lax342547.SelectedRemoval Lax342547.PairedRecipes Lax342547.RecipeResiduals
open Lax342547.PinLabelExclusions Lax342547.ProjectedPins
open Lax342547.RawBaselines

omit [Fintype H] in
/--
---
conclusion: Lax342547.ResponseSolvability.selected_part_correct
---
Each selected witness is one of the endpoint atoms. The finite linear combination therefore belongs to the selected-atom span in the correct space.
-/
theorem selected_part_correct (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) (i : Fin 2) :
    selectedPart W c i ∈ correctSpace W P i := by
  classical
  apply (show Submodule.span Binary
    (Set.range (fun x : Position W i => (endpointAtoms W i x).profile)) ≤
      correctSpace W P i from le_sup_right)
  apply Submodule.sum_mem
  intro u _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rcases u with ⟨z, t⟩
  fin_cases z
  · exact ⟨Sum.inl t, rfl⟩
  · exact ⟨Sum.inr t, rfl⟩

/--
---
conclusion: Lax342547.ResponseSolvability.obstruction_correct
---
Use the proved full obstruction decomposition. The remainder lies in the effective profile space and the selected part lies in the endpoint atom span.
-/
theorem obstruction_correct {K : ℕ} (hk : 0 < k) (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∀ i, x i ∈ correctSpace W P i := by
  obtain ⟨c, hc⟩ := Lax342547Proofs.EffectiveObstructions.obstruction_decomposition hk W P Q hK
    A hA hfresh U V hU hV T hT F hF z x h hdegree
  intro i
  have heff : (x - selectedPart W c) i ∈ correctSpace W P i :=
    (show effective (Profile k n b degree) P i ≤ correctSpace W P i from le_sup_left) (hc i)
  have hsum := (correctSpace W P i).add_mem heff (selected_part_correct W P c i)
  simpa only [Pi.sub_apply, sub_add_cancel] using hsum

/--
---
conclusion: Lax342547.ResponseSolvability.unrestricted_solution
---
Every full obstruction belongs to the correct spaces at both endpoints. The target vanishes there, so double annihilation yields an unrestricted pure and derivative response realizing it on the whole actual profile-pair space.
-/
theorem unrestricted_solution {K : ℕ} (hk : 0 < k) (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree)
    (t : Fin 2 → Module.Dual Binary (Profile k n b degree))
    (ht : ∀ i, correctSpace W P i ≤ LinearMap.ker (t i)) :
    ∃ β δ ε, fullResponse W P Q U V F z β δ ε = ∑ i, (t i).comp (LinearMap.proj i) := by
  apply solvable_of_annihilator_zero
  intro x hx
  have hc := obstruction_correct hk W P Q hK A hA hfresh U V hU hV T hT F hF z x hx hdegree
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact LinearMap.mem_ker.mp (ht i (hc i))

/--
---
conclusion: Lax342547.ResponseSolvability.recipe_solution
---
The actual scalar recipe, frozen baseline and selected gradient prescriptions make both endpoint residuals vanish on their correct spaces. The proved obstruction reduction and duality construct a full response realizing this actual recipe residual.
-/
theorem recipe_solution [Fintype N] {K : ℕ} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i))
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (z : Fin 2) :
    ∃ β δ ε, fullResponse W P Q U V F z β δ ε =
      ∑ i, (residual W D L R F i z).comp (LinearMap.proj i) := by
  apply unrestricted_solution hk W P Q hK A hA hfresh U V hU hV T hT F hF z hdegree
  intro i
  exact Lax342547Proofs.RecipeResiduals.residual_correct W D L R oA oB T A B F
    hrecipe hF hfrozen hkeys hgradients i z

end Lax342547Proofs.ResponseSolvability
