import Lax793645Proofs.Simplifications.LowRankGramFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- All three free corners are retained in their original coordinates. -/
def tripleCoordinates (K : Type) : Vec (Fin 3×K)≃(Vec K×(Vec K×Vec K)) where
  toFun x := (fun i=>x (0,i),fun i=>x (1,i),fun i=>x (2,i))
  invFun z c := ![z.1,z.2.1,z.2.2] c.1 c.2
  left_inv x := by funext c; rcases c with ⟨a,i⟩; fin_cases a <;> rfl
  right_inv z := rfl

theorem triple_average {K : Type} [Fintype K] [DecidableEq K]
    (f : Vec K→Vec K→Vec K→ℝ) :
    avg unif (fun x : Vec (Fin 3×K)=>f (fun i=>x (0,i)) (fun i=>x (1,i)) (fun i=>x (2,i)))=
      avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>f x y z))) := by
  have hh := mapW_avg unif (tripleCoordinates K) (fun z=>f z.1 z.2.1 z.2.2)
  rw [unif_equiv,pair_unif,pairW_avg] at hh
  rw [pair_unif] at hh
  simp_rw [pairW_avg] at hh
  exact hh.symm

theorem triple_character {K : Type} [Fintype K]
    (ξ x : Vec (Fin 3×K)) :
    vectorPhase ξ x=vectorPhase (fun i=>ξ (0,i)) (fun i=>x (0,i))*
      vectorPhase (fun i=>ξ (1,i)) (fun i=>x (1,i))*
      vectorPhase (fun i=>ξ (2,i)) (fun i=>x (2,i)) := by
  unfold vectorPhase dotProduct
  rw [Fintype.sum_prod_type,Fin.sum_univ_three,wsign_add,wsign_add]

abbrev CornerCoordinates (I : Type) (N : ℕ) := Fin 3×(Fin N×(Bool×I))

def gramCornerBatch (D : Wgt (KeyCoordinates I N))
    (A A' B B' C C' M0 M1 M2 : Mat I I) (x : Vec (CornerCoordinates I N)) : ℝ :=
  let u : KeyCoordinates I N := fun i=>x (0,i)
  let v : KeyCoordinates I N := fun i=>x (1,i)
  let w : KeyCoordinates I N := fun i=>x (2,i)
  D u*D v*D w*D (u+v+w)*
    wsign (crossGram A A' N u v+crossGram B B' N u w+crossGram C C' N v w+
      gramPrimitive M0 u+gramPrimitive M1 v+gramPrimitive M2 w)

/-- Every linear Fourier coefficient of a full allowed four-corner batch
is small. This is the form needed for relations joining arbitrary batches. -/
theorem gram_corner_batch_fourier (E : Rail I) (Z : Vec E)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (A A' B B' C C' M0 M1 M2 : Mat I I)
    (hA : withinRail A E) (h0 : withinRail M0 E)
    (h1 : withinRail M1 E) (h2 : withinRail M2 E)
    (ξ : Vec (CornerCoordinates I N)) :
    |linearFourier (gramCornerBatch D A A' B B' C C' M0 M1 M2) ξ|≤
      δ^2+bp (-(N:ℝ)/2) := by
  unfold linearFourier
  simp_rw [triple_character]
  let F (u v w : KeyCoordinates I N) :=
    vectorPhase (fun i=>ξ (0,i)) u*vectorPhase (fun i=>ξ (1,i)) v*
    vectorPhase (fun i=>ξ (2,i)) w*(D u*D v*D w*D (u+v+w)*
      wsign (crossGram A A' N u v+crossGram B B' N u w+crossGram C C' N v w+
        gramPrimitive M0 u+gramPrimitive M1 v+gramPrimitive M2 w))
  change |avg unif (fun x : Vec (CornerCoordinates I N)=>F (fun i=>x (0,i)) (fun i=>x (1,i)) (fun i=>x (2,i)))|≤_
  rw [triple_average (K:=Fin N×(Bool×I)) F]
  have hh := full_allowed_gram_four_corner E Z D δ hδ hD hs hF
    A A' B B' C C' M0 M1 M2 hA h0 h1 h2
    (fun i=>ξ (0,i)) (fun i=>ξ (1,i)) (fun i=>ξ (2,i))
  convert hh using 1
  congr 1
  apply avg_congr
  intro x _
  apply avg_congr
  intro y _
  apply avg_congr
  intro z _
  dsimp only [F]
  ring

/-- Coefficients for one batch, in the original ordered plus/minus mask. -/
structure CornerGramPattern (I : Type) where
  a : Mat I I
  a' : Mat I I
  b : Mat I I
  b' : Mat I I
  c : Mat I I
  c' : Mat I I
  own0 : Mat I I
  own1 : Mat I I
  own2 : Mat I I

def CornerGramPattern.permitted (P : CornerGramPattern I) (E : Rail I) : Prop :=
  withinRail P.a E ∧ withinRail P.own0 E ∧ withinRail P.own1 E ∧ withinRail P.own2 E

def CornerGramPattern.batch (P : CornerGramPattern I) (D : Wgt (KeyCoordinates I N)) :
    Wgt (Vec (CornerCoordinates I N)) :=
  gramCornerBatch D P.a P.a' P.b P.b' P.c P.c' P.own0 P.own1 P.own2

/-- An arbitrary bounded-Fourier-norm joint weight retains the small factor
from every allowed batch. No independence of nominal columns is assumed here. -/
theorem retained_batches_weight {T : Type} [Fintype T] [DecidableEq T]
    (E : Rail I) (Z : Vec E) (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (P : T→CornerGramPattern I) (hP : ∀ t,(P t).permitted E)
    (w : Wgt (Vec (T×CornerCoordinates I N))) :
    |avg unif (fun x=>(∏ t:T,(P t).batch D (fun i=>x (t,i)))*w x)|≤
      (δ^2+bp (-(N:ℝ)/2))^Fintype.card T*fourierNorm w := by
  have hf t ξ : |linearFourier ((P t).batch D) ξ|≤δ^2+bp (-(N:ℝ)/2) :=
    gram_corner_batch_fourier E Z D δ hδ hD hs hF
      (P t).a (P t).a' (P t).b (P t).b' (P t).c (P t).c'
      (P t).own0 (P t).own1 (P t).own2
      (hP t).1 (hP t).2.1 (hP t).2.2.1 (hP t).2.2.2 ξ
  simpa using fourier_product_weight (fun t=>(P t).batch D)
    (fun _=>δ^2+bp (-(N:ℝ)/2)) hf w

/-- The same estimate after imposing any linear relations across the
original batches. The relation indicator has Fourier norm exactly one.
Conditioning normalization is deliberately kept outside this inequality. -/
theorem retained_batches_relations {T J : Type} [Fintype T] [DecidableEq T]
    [Fintype J] [DecidableEq J]
    (E : Rail I) (Z : Vec E) (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (P : T→CornerGramPattern I) (hP : ∀ t,(P t).permitted E)
    (A : Mat J (T×CornerCoordinates I N))
    (w : Wgt (Vec (T×CornerCoordinates I N))) :
    |avg unif (fun x=>(∏ t:T,(P t).batch D (fun i=>x (t,i)))*w x*ind (A*ᵥx=0))|≤
      (δ^2+bp (-(N:ℝ)/2))^Fintype.card T*fourierNorm w := by
  have hh := retained_batches_weight E Z D δ hδ hD hs hF P hP
    (fun x=>w x*ind (A*ᵥx=0))
  have hn : fourierNorm (fun x=>w x*ind (A*ᵥx=0))≤fourierNorm w := by
    simpa only [fourier_norm_kernel_eq_one,mul_one] using
      fourier_norm_mul w (fun x=>ind (A*ᵥx=0))
  simp only [←mul_assoc] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hn
    (pow_nonneg (add_nonneg (sq_nonneg _) (bp_pos _).le) _))

/-- The low-rank correction costs only 2^(N rank M), while every batch
retains its small Fourier factor, even after arbitrary cross-batch relations. -/
theorem retained_batches_low_rank {T J K : Type} [Fintype T] [DecidableEq T]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (E : Rail I) (Z : Vec E) (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (P : T→CornerGramPattern I) (hP : ∀ t,(P t).permitted E)
    (A : Mat J (T×CornerCoordinates I N)) (M : Mat K K)
    (L : Vec (T×CornerCoordinates I N)→ₗ[F] KeyCoordinates K N) :
    |avg unif (fun x=>(∏ t:T,(P t).batch D (fun i=>x (t,i)))*
      wsign (gramPrimitive M (L x))*ind (A*ᵥx=0))|≤
      (δ^2+bp (-(N:ℝ)/2))^Fintype.card T*bp ((N:ℝ)*M.rank) := by
  have hh := retained_batches_relations E Z D δ hδ hD hs hF P hP A
    (fun x=>wsign (gramPrimitive M (L x)))
  have hn := fourier_norm_linear_pullback (LinearMap.toMatrix' L)
    (fun x=>wsign (gramPrimitive M x))
  have he x : (LinearMap.toMatrix' L)*ᵥx=L x := LinearMap.congr_fun (toMat_map L) x
  simp only [he] at hn
  exact hh.trans (mul_le_mul_of_nonneg_left (hn.trans (low_rank_gram_fourier_norm M))
    (pow_nonneg (add_nonneg (sq_nonneg _) (bp_pos _).le) _))

end
end Lax793645Proofs.Simplifications
