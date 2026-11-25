import Lax793645Proofs.Simplifications.FiniteCellOverlap
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X Y I J : Type} [AddCommGroup X] [Module F X] [Fintype X]
  [AddCommGroup Y] [Module F Y] [Fintype Y]
  [AddCommGroup I] [Module F I] [Fintype I]
  [AddCommGroup J] [Module F J] [Fintype J]

/-- Prescribing b affine bits at an attainable point of a key fiber
retains at least a fraction 2^(-b) of that fiber. -/
theorem affine_key_slice_mass {b : ℕ} (K : X →ₗ[F] I) (A : X →ₗ[F] Vec (Fin b))
    (x₀ : X) : bp (-(b:ℝ))*pr unif (fun x=>K x=K x₀) ≤
      pr unif (fun x=>K x=K x₀ ∧ A x=A x₀) := by
  let T := K.rangeRestrict.prod A
  let : Fintype K.range := Fintype.ofFinite _
  have he : (fun x=>K x=K x₀ ∧ A x=A x₀)=(fun x=>T x=T x₀) := by
    funext x
    exact propext ⟨fun h=>Prod.ext (Subtype.ext h.1) h.2,
      fun h=>⟨congrArg (fun z : K.range × Vec (Fin b)=>(z.1:I)) h,congrArg Prod.snd h⟩⟩
  rw [he,pr_unif_lin,pr_unif_lin,ind_one (mem_range_self _ _),ind_one (mem_range_self _ _),
    one_mul,one_mul,←bp_add]
  have hr : rk T≤rk K+b := by
    simpa [rk,dim,Vec,Module.finrank_prod] using T.range.finrank_le
  apply bp_le
  exact_mod_cast (show -(b:ℤ) + -(rk K:ℤ) ≤ -(rk T:ℤ) by omega)

def twoPositionMass {b : ℕ} (K : X →ₗ[F] I) (L : Y →ₗ[F] J)
    (s : X→Y→Vec (Fin b)) (v : Vec (Fin b)) (k : I×J) :=
  pr (pairW unif unif) (fun xy=>K xy.1=k.1 ∧ L xy.2=k.2 ∧ s xy.1 xy.2=v)

def twoPositionFeasible {b : ℕ} (K : X →ₗ[F] I) (L : Y →ₗ[F] J)
    (s : X→Y→Vec (Fin b)) (v : Vec (Fin b)) (k : I×J) :=
  ∃ x y,K x=k.1 ∧ L y=k.2 ∧ s x y=v

/-- Work on the two actual key fibers. Each separately affine binary
prescription is imposed first at a witness in the second slot, then on
the whole second fiber. Empty fibers contribute zero. -/
theorem two_position_accepted_mass {b : ℕ} (K : X →ₗ[F] I) (L : Y →ₗ[F] J)
    (s : X→Y→Vec (Fin b))
    (hx : ∀ y,∃ (A : X →ₗ[F] Vec (Fin b)) (d : Vec (Fin b)),∀ x,s x y=A x+d)
    (hy : ∀ x,∃ (A : Y →ₗ[F] Vec (Fin b)) (d : Vec (Fin b)),∀ y,s x y=A y+d)
    (v : Vec (Fin b)) (k : I×J) :
    (bp (-(b:ℝ)))^2 * (pr unif (fun x=>K x=k.1) * pr unif (fun y=>L y=k.2)) *
      ind (twoPositionFeasible K L s v k) ≤ twoPositionMass K L s v k := by
  classical
  by_cases hf : twoPositionFeasible K L s v k
  · rw [ind_one hf,mul_one]
    obtain ⟨x₀,y₀,hx₀,hy₀,hv⟩:=hf
    let P (x : X) := K x=k.1 ∧ s x y₀=v
    let c := bp (-(b:ℝ))
    let a := pr unif (fun x=>K x=k.1)
    let d := pr unif (fun y=>L y=k.2)
    obtain ⟨A,t,hA⟩:=hx y₀
    have hp : c*a≤pr unif P := by
      simpa only [P,c,a,←hx₀,←hv,hA,add_left_inj] using affine_key_slice_mass K A x₀
    have hsecond (x : X) : ind (P x)*(c*d) ≤
        pr unif (fun y=>K x=k.1 ∧ L y=k.2 ∧ s x y=v) := by
      by_cases hg : P x
      · obtain ⟨B,t,hB⟩:=hy x
        rw [ind_one hg,one_mul]
        simpa only [hg.1,true_and,←hy₀,←hg.2,hB,add_left_inj,c,d] using affine_key_slice_mass L B y₀
      rw [ind_zero hg,zero_mul]
      exact pr_nonneg unif_law.nz
    have h:=avg_mono unif_law.nz hsecond
    rw [avg_mul] at h
    change pr unif P*(c*d)≤_ at h
    have hcd : 0≤c*d := mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)
    have H:=mul_le_mul_of_nonneg_right hp hcd
    unfold twoPositionMass pr
    rw [pairW_avg]
    change c^2*(a*d)≤_
    exact (by ring : c^2*(a*d)=(c*a)*(c*d)).le.trans (H.trans h)
  rw [ind_zero hf,mul_zero]
  exact pr_nonneg (pairW_law unif_law unif_law).nz

structure TwoPositionQuery (X Y I J : Type) [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] [AddCommGroup I] [Module F I]
    [AddCommGroup J] [Module F J] (bits : ℕ) where
  leftKey : X →ₗ[F] I
  rightKey : Y →ₗ[F] J
  offset : I × J
  test : X→Y→Vec (Fin bits)
  leftAffine : ∀ y,∃ (A : X →ₗ[F] Vec (Fin bits)) (d : Vec (Fin bits)),∀ x,test x y=A x+d
  rightAffine : ∀ x,∃ (A : Y →ₗ[F] Vec (Fin bits)) (d : Vec (Fin bits)),∀ y,test x y=A y+d
  target : Vec (Fin bits)

namespace TwoPositionQuery
variable {bits : ℕ} (D : TwoPositionQuery X Y I J bits)

def accepted (k : I×J) := twoPositionMass D.leftKey D.rightKey D.test D.target (k-D.offset)

def statusMass (P : X→Prop) (Q : Y→Prop) (k : I×J) :=
  pr (pairW unif unif) (fun xy=>D.leftKey xy.1=(k-D.offset).1 ∧
    D.rightKey xy.2=(k-D.offset).2 ∧ P xy.1 ∧ Q xy.2 ∧ D.test xy.1 xy.2=D.target)

def statusFiberMass (r t : ℕ) (P : X→Prop) (Q : Y→Prop) (k : I×J) :=
  (bp (-(bits:ℝ)))^2 * ((bp (-(r:ℝ))*pr unif (fun x=>D.leftKey x=(k-D.offset).1)) *
    (bp (-(t:ℝ))*pr unif (fun y=>D.rightKey y=(k-D.offset).2))) * ind (0<D.statusMass P Q k)

/-- The unrestricted probability of the two keys, counted only when the
prescribed binary tests have a simultaneous solution at those keys. -/
def feasibleMass (k : I×J) := (bp (-(bits:ℝ)))^2 *
    (pr unif (fun x=>D.leftKey x=(k-D.offset).1) * pr unif (fun y=>D.rightKey y=(k-D.offset).2)) *
    ind (twoPositionFeasible D.leftKey D.rightKey D.test D.target (k-D.offset))

theorem feasible_le_accepted (k : I×J) : 0≤D.feasibleMass k ∧ D.feasibleMass k≤D.accepted k :=
  ⟨mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (pr_nonneg unif_law.nz) (pr_nonneg unif_law.nz)))
    (ind_nonneg _),two_position_accepted_mass _ _ _ D.leftAffine D.rightAffine _ _⟩

/-- Freeze the unary coordinates at one feasible input pair. Each lost
coordinate costs at most a factor of two, also on the original key fiber. -/
theorem status_witness_mass {r t : ℕ} (L : X→ₗ[F]Vec (Fin r)) (M : Y→ₗ[F]Vec (Fin t))
    (P : X→Prop) (Q : Y→Prop) (x₀ : X) (y₀ : Y)
    (hp : ∀ x,L x=L x₀→P x) (hq : ∀ y,M y=M y₀→Q y) (hs : D.test x₀ y₀=D.target) :
    (bp (-(bits:ℝ)))^2 *
        ((bp (-(r:ℝ))*pr unif (fun x=>D.leftKey x=D.leftKey x₀)) *
         (bp (-(t:ℝ))*pr unif (fun y=>D.rightKey y=D.rightKey y₀))) ≤
      pr (pairW unif unif) (fun u=>D.leftKey u.1=D.leftKey x₀ ∧ D.rightKey u.2=D.rightKey y₀ ∧
        P u.1 ∧ Q u.2 ∧ D.test u.1 u.2=D.target) := by
  let A:=D.leftKey.prod L
  let B:=D.rightKey.prod M
  have ha : bp (-(r:ℝ))*pr unif (fun x=>D.leftKey x=D.leftKey x₀)≤pr unif (fun x=>A x=A x₀) := by
    simpa only [A,LinearMap.prod_apply,Function.prod,Prod.mk.injEq] using affine_key_slice_mass D.leftKey L x₀
  have hb : bp (-(t:ℝ))*pr unif (fun y=>D.rightKey y=D.rightKey y₀)≤pr unif (fun y=>B y=B y₀) := by
    simpa only [B,LinearMap.prod_apply,Function.prod,Prod.mk.injEq] using affine_key_slice_mass D.rightKey M y₀
  have H:=two_position_accepted_mass A B D.test D.leftAffine D.rightAffine D.target (A x₀,B y₀)
  rw [ind_one (show twoPositionFeasible A B D.test D.target (A x₀,B y₀) from ⟨x₀,y₀,rfl,rfl,hs⟩),mul_one] at H
  refine (mul_le_mul_of_nonneg_left (mul_le_mul ha hb
    (mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)) (pr_nonneg unif_law.nz)) (sq_nonneg _)).trans (H.trans ?_)
  apply pr_mono (pairW_law unif_law unif_law).nz
  rintro ⟨x,y⟩ ⟨h₁,h₂,h₃⟩
  exact ⟨congrArg Prod.fst h₁,congrArg Prod.fst h₂,hp x (congrArg Prod.snd h₁),
    hq y (congrArg Prod.snd h₂),h₃⟩

/-- A support bound at the observed keys, including both unary filters. -/
theorem status_fiber_le_mass {r t : ℕ} (L : X→ₗ[F]Vec (Fin r)) (M : Y→ₗ[F]Vec (Fin t))
    (P : X→Prop) (Q : Y→Prop) (hp : ∀ x a,L x=L a→P a→P x) (hq : ∀ y a,M y=M a→Q a→Q y)
    (k : I×J) : 0≤D.statusFiberMass r t P Q k ∧ D.statusFiberMass r t P Q k≤D.statusMass P Q k := by
  unfold statusFiberMass
  have law := pairW_law (unif_law (α:=X)) (unif_law (α:=Y))
  refine ⟨mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
    (mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz))
    (mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)))) (ind_nonneg _),?_⟩
  by_cases h : 0<D.statusMass P Q k
  · rw [ind_one h,mul_one]
    obtain ⟨⟨x,y⟩,⟨h₁,h₂,hP,hQ,h₃⟩,_⟩:=exists_of_pr_pos law.nz h
    have H:=D.status_witness_mass L M P Q x y (fun z hz=>hp z x hz hP) (fun z hz=>hq z y hz hQ) h₃
    simpa only [statusMass,h₁,h₂] using H
  rw [ind_zero h,mul_zero]
  exact pr_nonneg law.nz

end TwoPositionQuery

/-- Unary status restrictions on the two inputs of a binary script. -/
structure TwoPositionRequest (X Y I J : Type) [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] [AddCommGroup I] [Module F I]
    [AddCommGroup J] [Module F J] (bits : ℕ) extends TwoPositionQuery X Y I J bits where
  leftCount : ℕ
  rightCount : ℕ
  leftRows : X→ₗ[F]Vec (Fin leftCount)
  rightRows : Y→ₗ[F]Vec (Fin rightCount)
  leftAllowed : Vec (Fin leftCount)→Prop
  rightAllowed : Vec (Fin rightCount)→Prop

namespace TwoPositionRequest
variable {b : ℕ} (D : TwoPositionRequest X Y I J b)
def actual := D.toTwoPositionQuery.statusMass (D.leftAllowed ∘ D.leftRows) (D.rightAllowed ∘ D.rightRows)
def lower := D.toTwoPositionQuery.statusFiberMass D.leftCount D.rightCount
  (D.leftAllowed ∘ D.leftRows) (D.rightAllowed ∘ D.rightRows)

theorem lower_le_actual (k : I×J) : 0≤D.lower k ∧ D.lower k≤D.actual k :=
  D.toTwoPositionQuery.status_fiber_le_mass D.leftRows D.rightRows _ _
    (fun _ _ h hx=>(congrArg D.leftAllowed h).mpr hx)
    (fun _ _ h hy=>(congrArg D.rightAllowed h).mpr hy) k
end TwoPositionRequest

/-- Multiplying the two per-key lower bounds before averaging gives the
actual accepted overlap. Both filters may use the two leaf indices. -/
theorem filtered_key_overlap_lower {A B K : Type} [Fintype A] [Fintype B] [Fintype K]
    (ν : Wgt K) (ha : ∀ k,0≤ν k) (μ : Wgt A) (δ : Wgt B)
    (hm : ∀ a,0≤μ a) (hd : ∀ b,0≤δ b)
    (a a₀ : A→Wgt K) (b b₀ : B→Wgt K)
    (hA : ∀ i k,0≤a₀ i k ∧ a₀ i k≤a i k)
    (hB : ∀ i k,0≤b₀ i k ∧ b₀ i k≤b i k) :
    overlap ν (fun k=>avg μ (fun i=>a₀ i k)) (fun k=>avg δ (fun i=>b₀ i k)) ≤
      overlap ν (fun k=>avg μ (fun i=>a i k)) (fun k=>avg δ (fun i=>b i k)) := by
  apply avg_mono ha
  intro k
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (avg_mono hm (fun i=>(hA i k).2)) (ha k)
  · exact div_le_div_of_nonneg_right (avg_mono hd (fun i=>(hB i k).2)) (ha k)
  · exact div_nonneg (avg_nonneg hd (fun i=>(hB i k).1)) (ha k)
  exact div_nonneg (avg_nonneg hm (fun i=>(hA i k).1.trans (hA i k).2)) (ha k)

/-- Draw independent leaves. The orientation filters and the entire requests
can use the two leaf indices. Unary restrictions can be arbitrary unions of
fibers of the recorded rows. The lower bound is unnormalized. -/
theorem two_position_filtered_overlap {L R A B : Type} [Fintype L] [Fintype R]
    [Fintype A] [Fintype B] {b₁ b₂ : ℕ} (l : Wgt L) (r : Wgt R)
    (hl : ∀ i,0≤l i) (hr : ∀ j,0≤r j) (ν : Wgt (I×J)) (hν : ∀ k,0≤ν k)
    (μ : L→Wgt A) (δ : R→Wgt B) (hμ : ∀ i a,0≤μ i a) (hδ : ∀ j b,0≤δ j b)
    (f : L×R→A→Prop) (g : L×R→B→Prop)
    (U : L×R→A→TwoPositionRequest X Y I J b₁) (V : L×R→B→TwoPositionRequest X Y I J b₂) :
    avg (pairW l r) (fun h=>overlap ν
      (fun k=>avg (subW (μ h.1) (f h)) (fun a=>(U h a).lower k))
      (fun k=>avg (subW (δ h.2) (g h)) (fun b=>(V h b).lower k))) ≤
    avg (pairW l r) (fun h=>overlap ν
      (fun k=>avg (subW (μ h.1) (f h)) (fun a=>(U h a).actual k))
      (fun k=>avg (subW (δ h.2) (g h)) (fun b=>(V h b).actual k))) := by
  apply avg_mono (w:=pairW l r) (fun h=>mul_nonneg (hl h.1) (hr h.2))
  intro h
  exact filtered_key_overlap_lower ν hν _ _ (fun a=>mul_nonneg (hμ _ a) (ind_nonneg _))
    (fun b=>mul_nonneg (hδ _ b) (ind_nonneg _)) _ _ _ _
    (fun a k=>(U h a).lower_le_actual k) (fun b k=>(V h b).lower_le_actual k)

private theorem fair_shift (u v : F) : pr unif (fun b : F=>u+b=v)=1/2 := by
  have he : (fun b : F=>u+b=v)=(fun b=>b=v-u) := funext fun b=>propext (by abel_nf; constructor <;> intro h <;> linear_combination h)
  rw [he,pr_point',unif_apply]
  norm_num [F]

/-- Balanced unary observations do not imply a collision of the two
accepted joint laws. B can in particular be a dot product of any rank. -/
theorem opposite_binary_queries {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (φ : A→B→F) :
    let bit (s : (A×F)×(B×F)) := φ s.1.1 s.2.1+s.1.2+s.2.2
    (∀ x t,pr unif (fun y=>bit (x,y)=t)=1/2) ∧
    (∀ y t,pr unif (fun x=>bit (x,y)=t)=1/2) ∧
    (∀ ν : Wgt ((A×F)×(B×F)),overlap ν (subW ν (fun s=>bit s=0))
      (subW ν (fun s=>bit s=1))=0) := by
  intro bit
  refine ⟨?_,?_,?_⟩
  · intro x t
    rw [pair_unif,pr,pairW_avg]
    change avg unif (fun y=>pr unif (fun b=>φ x.1 y+x.2+b=t))=_
    simp_rw [fair_shift]
    exact unif_law.avg_const _
  · intro y t
    rw [pair_unif,pr,pairW_avg]
    change avg unif (fun x=>pr unif (fun a=>φ x y.1+a+y.2=t))=_
    simp_rw [add_right_comm (φ _ _) _ y.2,fair_shift]
    exact unif_law.avg_const _
  intro ν
  unfold overlap avg
  apply sum_eq_zero
  intro x _
  rcases bit_cases (bit x) with h|h <;> simp [subW,density,h,ind]


end
end Lax793645Proofs.Simplifications
