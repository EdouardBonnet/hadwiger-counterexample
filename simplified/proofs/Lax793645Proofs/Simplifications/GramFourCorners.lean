import Lax793645Proofs.Simplifications.LinearRelationFourier
import Lax793645Proofs.Simplifications.FourCornerRank

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {N : ℕ}

abbrev KeyCoordinates (I : Type) (N : ℕ) := Vec (Fin N×(Bool×I))

def keyPlus : KeyCoordinates I N→ₗ[F] PlusRack I N where
  toFun x u i := x (u,(false,i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def keyMinus : KeyCoordinates I N→ₗ[F] PlusRack I N where
  toFun x u i := x (u,(true,i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def keyInsert (b : Bool) : PlusRack I N→ₗ[F] KeyCoordinates I N where
  toFun X c := if c.2.1=b then X c.1 c.2.2 else 0
  map_add' X Y := by ext c; by_cases h : c.2.1=b <;> simp [h]
  map_smul' a X := by ext c; by_cases h : c.2.1=b <;> simp [h]

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem plus_insert_false (X : PlusRack I N) : keyPlus (keyInsert false X)=X := by
  ext u i; rfl
omit [Fintype I] [DecidableEq I] in
@[simp]
theorem minus_insert_false (X : PlusRack I N) : keyMinus (keyInsert false X)=0 := by
  ext u i; rfl
omit [Fintype I] [DecidableEq I] in
@[simp]
theorem plus_insert_true (X : PlusRack I N) : keyPlus (keyInsert true X)=0 := by
  ext u i; rfl
omit [Fintype I] [DecidableEq I] in
@[simp]
theorem minus_insert_true (X : PlusRack I N) : keyMinus (keyInsert true X)=X := by
  ext u i; rfl

def crossGram (A B : Mat I I) (N : ℕ) :
    KeyCoordinates I N→ₗ[F] KeyCoordinates I N→ₗ[F] F :=
  (layerPhase A N).compl₁₂ keyPlus keyMinus+
    ((layerPhase B N).compl₁₂ keyPlus keyMinus).flip

omit [DecidableEq I] in
theorem cross_gram_apply (A B : Mat I I) (x y : KeyCoordinates I N) :
    crossGram A B N x y=
      layerPhase A N (keyPlus x) (keyMinus y)+
      layerPhase B N (keyPlus y) (keyMinus x) := rfl

omit [DecidableEq I] in
theorem cross_gram_add (A B C D : Mat I I) :
    crossGram A B N+crossGram C D N=crossGram (A+C) (B+D) N := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.add_apply,cross_gram_apply,layer_form,mpair_add]
  abel

omit [DecidableEq I] in
theorem cross_gram_flip (A B : Mat I I) :
    (crossGram A B N).flip=crossGram B A N := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.flip_apply,cross_gram_apply]
  abel

theorem bilinear_restriction_rank {V W A B : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    (b : V→ₗ[F] W→ₗ[F] F) (f : A→ₗ[F] V) (g : B→ₗ[F] W) :
    rk (b.compl₁₂ f g)≤rk b := by
  change rk (g.dualMap.comp (b.comp f))≤rk b
  exact (rk_comp_le_right (b.comp f) g.dualMap).trans (rk_comp_le_left f b)

omit [DecidableEq I] in
theorem cross_gram_rank_left (A B : Mat I I) : N*A.rank≤rk (crossGram A B N) := by
  have he : (crossGram A B N).compl₁₂ (keyInsert false) (keyInsert true)=layerPhase A N := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    change crossGram A B N (keyInsert false X) (keyInsert true Y)=layerPhase A N X Y
    simp only [cross_gram_apply,plus_insert_false,minus_insert_true,plus_insert_true,
      minus_insert_false,map_zero,add_zero]
  have hh := bilinear_restriction_rank (crossGram A B N) (keyInsert false) (keyInsert true)
  rwa [he,layer_rank] at hh

theorem cross_gram_rank_right (A B : Mat I I) : N*B.rank≤rk (crossGram A B N) := by
  have hh := cross_gram_rank_left (N:=N) B A
  rw [←cross_gram_flip,bilinear_flip_rank] at hh
  exact hh

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem nonzero_matrix_rank (A : Mat I J) (hA : A≠0) : 1≤A.rank := by
  have h : A.rank≠0 := by
    intro hz
    apply hA
    apply coe_mv_inj
    change A.mulVecLin=(0 : Mat I J).mulVecLin
    rw [Matrix.mulVecLin_zero]
    rw [←LinearMap.range_eq_bot]
    exact (Submodule.finrank_eq_zero (R:=F)).mp hz
  omega

theorem cross_gram_rank_nonzero (A B : Mat I I) (h : A≠0 ∨ B≠0) :
    N≤rk (crossGram A B N) := by
  rcases h with h|h
  · exact (show N≤N*A.rank by simpa using Nat.mul_le_mul_left N (nonzero_matrix_rank A h)).trans
      (cross_gram_rank_left A B)
  · exact (show N≤N*B.rank by simpa using Nat.mul_le_mul_left N (nonzero_matrix_rank B h)).trans
      (cross_gram_rank_right A B)

def gramPrimitive (M : Mat I I) (x : KeyCoordinates I N) : F :=
  layerPhase M N (keyPlus x) (keyMinus x)

omit [DecidableEq I] in
theorem gram_primitive_four_corner (M : Mat I I) (x y z : KeyCoordinates I N) :
    crossGram M M N x y+crossGram M M N x z+crossGram M M N y z=
      gramPrimitive M x+gramPrimitive M y+gramPrimitive M z+gramPrimitive M (x+y+z) := by
  simp only [cross_gram_apply,gramPrimitive,map_add,LinearMap.add_apply]
  ring_nf
  have ht : (2 : F)=0 := by decide
  simp only [ht,mul_zero,add_zero]

omit [Fintype I] in
theorem ledger_recovers (E : Rail I) (M : Mat I I) (hM : withinRail M E) :
    ledgerM E (railsM E M)=M := by
  classical
  ext i j
  by_cases h : (i,j)∈E
  · simp only [ledgerM,Matrix.of_apply,dif_pos h,railsM]
  · simp only [ledgerM,Matrix.of_apply,dif_neg h,hM i j h]

/-- A supported Gram coefficient gives a constant quadratic phase on the
whole prescribed Gram variety, including off-position plus/minus products. -/
theorem gram_primitive_fixed (E : Rail I) (Z : Vec E) (M : Mat I I)
    (hM : withinRail M E) (x : KeyCoordinates I N)
    (hx : traced (keyPlus x,keyMinus x) E Z) :
    wsign (gramPrimitive M x)=vectorPhase (railsM E M) Z := by
  have hh := phased_match (keyPlus x,keyMinus x) E Z (railsM E M) hx
  rw [ledger_recovers E M hM] at hh
  exact hh

/-- The resonant phase cancels exactly on the four supported corners. -/
theorem supported_resonance (E : Rail I) (Z : Vec E) (M : Mat I I)
    (hM : withinRail M E) (D : Wgt (KeyCoordinates I N))
    (hD : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (x y z : KeyCoordinates I N) :
    D x*D y*D z*D (x+y+z)*
      wsign (crossGram M M N x y+crossGram M M N x z+crossGram M M N y z)=
      D x*D y*D z*D (x+y+z) := by
  by_cases hx : D x=0
  · simp [hx]
  by_cases hy : D y=0
  · simp [hy]
  by_cases hz : D z=0
  · simp [hz]
  by_cases hw : D (x+y+z)=0
  · simp [hw]
  rw [gram_primitive_four_corner]
  simp only [wsign_add,gram_primitive_fixed E Z M hM x (hD x hx),
    gram_primitive_fixed E Z M hM y (hD y hy),
    gram_primitive_fixed E Z M hM z (hD z hz),
    gram_primitive_fixed E Z M hM (x+y+z) (hD _ hw)]
  have hh := wsign_abs (dotProduct (railsM E M) Z)
  change D x*D y*D z*D (x+y+z)*(vectorPhase (railsM E M) Z*
    vectorPhase (railsM E M) Z*vectorPhase (railsM E M) Z*vectorPhase (railsM E M) Z)=_
  have hc : vectorPhase (railsM E M) Z^2=1 := by
    change wsign (dotProduct (railsM E M) Z)^2=1
    nlinarith [sq_abs (wsign (dotProduct (railsM E M) Z))]
  have he : vectorPhase (railsM E M) Z*vectorPhase (railsM E M) Z*
      vectorPhase (railsM E M) Z*vectorPhase (railsM E M) Z=1 := by nlinarith [sq_nonneg (vectorPhase (railsM E M) Z^2-1)]
  rw [he,mul_one]

/-- Either all six ordered cross-copy coefficients are the same primitive,
or a four-corner rank is at least the ambient dimension. -/
theorem gram_rank_alternative (A A' B B' C C' : Mat I I) :
    (A'=A ∧ B=A ∧ B'=A ∧ C=A ∧ C'=A) ∨
    N≤max (max (rk (crossGram A A' N+crossGram B B' N))
      (rk (crossGram A A' N+(crossGram C C' N).flip)))
      (rk (crossGram B B' N+crossGram C C' N)) := by
  rw [cross_gram_flip,cross_gram_add,cross_gram_add,cross_gram_add]
  let R := max (max (rk (crossGram (A+B) (A'+B') N))
    (rk (crossGram (A+C') (A'+C) N))) (rk (crossGram (B+C) (B'+C') N))
  change _ ∨ N≤R
  by_cases h : N≤R
  · exact Or.inr h
  left
  have vanish (M T : Mat I I) (hr : rk (crossGram M T N)≤R) : M=0 ∧ T=0 := by
    constructor
    · by_contra hm
      exact h ((cross_gram_rank_nonzero M T (Or.inl hm)).trans hr)
    · by_contra ht
      exact h ((cross_gram_rank_nonzero M T (Or.inr ht)).trans hr)
  have h1 := vanish (A+B) (A'+B') ((le_max_left _ _).trans (le_max_left _ _))
  have h2 := vanish (A+C') (A'+C) ((le_max_right _ _).trans (le_max_left _ _))
  have h3 := vanish (B+C) (B'+C') (le_max_right _ _)
  have eq (X Y : Mat I I) : X+Y=0 ↔ X=Y := by
    rw [←ZModModule.sub_eq_add,sub_eq_zero]
  simp only [eq] at h1 h2 h3
  exact ⟨h2.2.trans (h3.1.symm.trans h1.1.symm),h1.1.symm,
    h3.2.trans h2.1.symm,h3.1.symm.trans h1.1.symm,h2.1.symm⟩

/-- The allowed-Gram local estimate, including arbitrary linear phases.
The Gram support contains all ordered plus/minus products on the mask. -/
theorem allowed_gram_four_corner (E : Rail I) (Z : Vec E)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (A A' B B' C C' : Mat I I) (hA : withinRail A E)
    (ξ η ζ : KeyCoordinates I N) :
    |fourCorner (crossGram A A' N) (crossGram B B' N) (crossGram C C' N)
      (fun x=>vectorPhase ξ x*D x) (fun x=>vectorPhase η x*D x)
      (fun x=>vectorPhase ζ x*D x) D|≤δ^2+bp (-(N:ℝ)/2) := by
  let f (a : KeyCoordinates I N) (x : KeyCoordinates I N) := vectorPhase a x*D x
  have hf a x : |f a x|≤1 := by simpa only [f,abs_mul,vectorPhase,wsign_abs,one_mul] using hD x
  have hhat a ν : |linearFourier (f a) ν|≤δ := by
    rw [show f a=(fun x=>vectorPhase a x*D x) from rfl,linear_fourier_modulate]
    exact hF _
  rcases gram_rank_alternative (N:=N) A A' B B' C C' with he|hr
  · rcases he with ⟨h1,h2,h3,h4,h5⟩
    subst A'
    subst B
    subst B'
    subst C
    subst C'
    have hev : fourCorner (crossGram A A N) (crossGram A A N) (crossGram A A N)
        (f ξ) (f η) (f ζ) D=
        avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
          f ξ x*f η y*f ζ z*D (x+y+z)))) := by
      apply avg_congr
      intro x _
      apply avg_congr
      intro y _
      apply avg_congr
      intro z _
      calc
        _=(vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z)*
          (D x*D y*D z*D (x+y+z)*
            wsign (crossGram A A N x y+crossGram A A N x z+crossGram A A N y z)) := by
              dsimp only [f]; ring
        _=_ := by rw [supported_resonance E Z A hA D hs]; dsimp only [f]; ring
    change |fourCorner _ _ _ (f ξ) (f η) (f ζ) D|≤_
    rw [hev]
    exact (small_fourier_four_corner (f ξ) (f η) (f ζ) D δ hδ
      (hhat ξ) (hhat η) (hf ζ) hD).trans (le_add_of_nonneg_right (bp_pos _).le)
  · have hh := four_corner_max_rank (crossGram A A' N) (crossGram B B' N)
      (crossGram C C' N) (f ξ) (f η) (f ζ) D (hf ξ) (hf η) (hf ζ) hD
    refine hh.trans ((bp_le ?_).trans (le_add_of_nonneg_left (sq_nonneg δ)))
    exact div_le_div_of_nonneg_right (neg_le_neg (by exact_mod_cast hr)) (by norm_num)


/-- Multiplying a supported function by an allowed within-copy Gram phase
only multiplies it by a constant sign. -/
theorem supported_gram_modulation (E : Rail I) (Z : Vec E) (M : Mat I I)
    (hM : withinRail M E) (D : Wgt (KeyCoordinates I N))
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z) (x : KeyCoordinates I N) :
    D x*wsign (gramPrimitive M x)=D x*vectorPhase (railsM E M) Z := by
  by_cases h : D x=0
  · simp only [h,zero_mul]
  · rw [gram_primitive_fixed E Z M hM x (hs x h)]

/-- Full local estimate with the three within-copy phases retained. -/
theorem full_allowed_gram_four_corner (E : Rail I) (Z : Vec E)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (A A' B B' C C' M0 M1 M2 : Mat I I)
    (hA : withinRail A E) (h0 : withinRail M0 E)
    (h1 : withinRail M1 E) (h2 : withinRail M2 E)
    (ξ η ζ : KeyCoordinates I N) :
    |avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      D x*D y*D z*D (x+y+z)*vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z+
          gramPrimitive M0 x+gramPrimitive M1 y+gramPrimitive M2 z))))|≤
      δ^2+bp (-(N:ℝ)/2) := by
  let c := vectorPhase (railsM E M0) Z*vectorPhase (railsM E M1) Z*vectorPhase (railsM E M2) Z
  have he x y z :
      D x*D y*D z*D (x+y+z)*vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z+
          gramPrimitive M0 x+gramPrimitive M1 y+gramPrimitive M2 z)=
      c*((vectorPhase ξ x*D x)*(vectorPhase η y*D y)*(vectorPhase ζ z*D z)*D (x+y+z)*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z)) := by
    rw [wsign_add,wsign_add,wsign_add]
    calc
      _=(D x*wsign (gramPrimitive M0 x))*(D y*wsign (gramPrimitive M1 y))*
        (D z*wsign (gramPrimitive M2 z))*(D (x+y+z)*vectorPhase ξ x*vectorPhase η y*
          vectorPhase ζ z*wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z)) := by ring
      _=_ := by
        rw [supported_gram_modulation E Z M0 h0 D hs,
          supported_gram_modulation E Z M1 h1 D hs,supported_gram_modulation E Z M2 h2 D hs]
        dsimp only [c]; ring
  simp_rw [he,avg_mul']
  rw [abs_mul]
  have hc : |c|=1 := by simp only [c,abs_mul,vectorPhase,wsign_abs,one_mul]
  rw [hc,one_mul]
  exact allowed_gram_four_corner E Z D δ hδ hD hs hF A A' B B' C C' hA ξ η ζ

/-- Ambient coordinates for exactly the key type used by the query template. -/
def queryFromCoordinates {p : Shape} (t : Tagging p I) (N : ℕ)
    (x : KeyCoordinates (KeySlots p t) N) : Keys (p:=p) t N :=
  (scatter t N).symm (keyPlus x,keyMinus x)

theorem query_gram_trace {p : Shape} (t : Tagging p I) (q : I→F)
    (x : KeyCoordinates (KeySlots p t) N)
    (h : ownPart t q (queryFromCoordinates t N x)) :
    traced (keyPlus x,keyMinus x) (crowded (ownPort t)) (directions (ownPort t) (ownMap t q)) := by
  apply (match_crowd _ _ _).mpr
  simpa only [ownPart,queryFromCoordinates,Equiv.apply_symm_apply] using h

omit [DecidableEq I] in
theorem query_mask_inclusion {p : Shape} (t : Tagging p I) (aim : I→Bool) :
    crowded (globPort p t aim)⊆crowded (ownPort t) := by
  classical
  intro v hv
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  exact congrArg Prod.snd (mem_filter.mp hv).2

/-- The local estimate for the actual query mask. `ownPart` supplies every
same-component plus/minus Gram entry, not just the individual diagonal bits. -/
theorem query_allowed_gram_four_corner {p : Shape} (t : Tagging p I)
    [DecidableEq (KeySlots p t)] (aim : I→Bool)
    (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p t) N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→ ownPart t q (queryFromCoordinates t N x))
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (A A' B B' C C' : Mat (KeySlots p t) (KeySlots p t))
    (hA : withinRail A (crowded (globPort p t aim)))
    (ξ η ζ : KeyCoordinates (KeySlots p t) N) :
    |fourCorner (crossGram A A' N) (crossGram B B' N) (crossGram C C' N)
      (fun x=>vectorPhase ξ x*D x) (fun x=>vectorPhase η x*D x)
      (fun x=>vectorPhase ζ x*D x) D|≤δ^2+bp (-(N:ℝ)/2) := by
  classical
  apply allowed_gram_four_corner (crowded (ownPort t)) (directions (ownPort t) (ownMap t q))
    D δ hδ hD (fun x hx=>query_gram_trace t q x (hs x hx)) hF A A' B B' C C'
      _ ξ η ζ
  intro i j h
  exact hA i j (fun hh=>h (query_mask_inclusion t aim hh))

/-- Full four-corner estimate for the construction's own key variety and
component/endpoint mask, with within-copy and linear phases included. -/
theorem query_full_allowed_gram_four_corner {p : Shape} (t : Tagging p I)
    [DecidableEq (KeySlots p t)] (aim : I→Bool) (q : I→F)
    (D : Wgt (KeyCoordinates (KeySlots p t) N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→ ownPart t q (queryFromCoordinates t N x))
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (A A' B B' C C' M0 M1 M2 : Mat (KeySlots p t) (KeySlots p t))
    (hA : withinRail A (crowded (globPort p t aim)))
    (h0 : withinRail M0 (crowded (globPort p t aim)))
    (h1 : withinRail M1 (crowded (globPort p t aim)))
    (h2 : withinRail M2 (crowded (globPort p t aim)))
    (ξ η ζ : KeyCoordinates (KeySlots p t) N) :
    |avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      D x*D y*D z*D (x+y+z)*vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z+
          gramPrimitive M0 x+gramPrimitive M1 y+gramPrimitive M2 z))))|≤
      δ^2+bp (-(N:ℝ)/2) := by
  classical
  have widen (M : Mat (KeySlots p t) (KeySlots p t))
      (hM : withinRail M (crowded (globPort p t aim))) : withinRail M (crowded (ownPort t)) :=
    fun i j h=>hM i j (fun hh=>h (query_mask_inclusion t aim hh))
  exact full_allowed_gram_four_corner (crowded (ownPort t)) (directions (ownPort t) (ownMap t q))
    D δ hδ hD (fun x hx=>query_gram_trace t q x (hs x hx)) hF
    A A' B B' C C' M0 M1 M2 (widen A hA) (widen M0 h0) (widen M1 h1) (widen M2 h2) ξ η ζ

end
end Lax793645Proofs.Simplifications
