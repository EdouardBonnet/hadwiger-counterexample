import Lax793645Proofs.Simplifications.QueryCellRecentring
import Lax793645Proofs.Simplifications.TesterRestrictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

theorem sketch_uniform_cap (a : I→Tickets p) (hn : 2*p.r≤n)
    (x : I→Knobs p.g n) :
    sketchLaw p n a x≤(labFee p I)⁻¹*unif x := by
  unfold sketchLaw labFee
  rw [draws_unif]
  have he i : spins p n (x i)=unif (x i) := by rw [spins,←draws_unif]
  apply le_trans (Finset.prod_le_prod
    (fun i (_ : i∈univ)=>(ticketLaw n (a i) hn).nz (x i))
    (fun i _=>ticketCap n (a i) hn (x i)))
  simp_rw [Finset.prod_mul_distrib,he]
  simp only [Finset.prod_const,card_univ,inv_pow]
  exact le_rfl

theorem recenter_sketch_weight (H : Space (PairedKeys (Comp p.g) (Fin N)))
    (o : Orient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (a : I→Tickets p)
    (x : I→Knobs p.g n) (c : Module.Dual F H) :
    sketchLaw p n a (fun i=>recenterQuery H o l s f S (x i) c)=sketchLaw p n a x := by
  classical
  unfold sketchLaw prodW
  apply Finset.prod_congr rfl
  intro i _
  unfold rung
  dsimp only
  rw [onW_val,onW_val]
  have he : issued p (a i) (recenterQuery H o l s f S (x i) c) ↔ issued p (a i) (x i) := by
    unfold issued
    rw [recenter_query_punches]
  rw [he,spins,←draws_unif]
  rfl

theorem coherent_compound_uniform (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (S : Module.Dual F H→ₗ[F]Vec (Fin n))
    (u : Vec I) (hu : weightsAff u) :
    mapW (pairW unif unif) (fun x : (I→Knobs p.g n)×Module.Dual F H=>
      compound p (fun i=>recenterQuery H o l s f S (x.1 i) x.2) u)=spins p n := by
  classical
  let A:=compoundAll p n u
  have hA : Surjective A := by
    intro y
    refine ⟨fun _=>y,?_⟩
    change ∑ i,u i • y=y
    rw [←Finset.sum_smul,hu,one_smul]
  let B:=A.prodMap (LinearMap.id : Module.Dual F H→ₗ[F]Module.Dual F H)
  have hB : Surjective B := by
    rintro ⟨y,c⟩
    obtain ⟨x,hx⟩:=hA y
    exact ⟨(x,c),Prod.ext hx rfl⟩
  let Kfun : Knobs p.g n×Module.Dual F H→Knobs p.g n:=
    fun x=>recenterQuery H o l s f S x.1 x.2
  have he : (fun x : (I→Knobs p.g n)×Module.Dual F H=>
      compound p (fun i=>recenterQuery H o l s f S (x.1 i) x.2) u)=Kfun ∘ B := by
    funext x
    exact recenter_query_compound H o l s f S x.1 u hu x.2
  rw [he,←pair_unif,←mapW_nested,map_unif_surjective B hB,pair_unif]
  exact recenter_query_uniform H o l s f S

/-- All affine probes use the same randomly chosen cell. Each individual
probe retains the old fixed ticket cap, independent of the number of cells. -/
theorem coherent_sketch_point (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (S : Module.Dual F H→ₗ[F]Vec (Fin n))
    (a : I→Tickets p) (hn : 2*p.r≤n) (u : Vec I) (hu : weightsAff u)
    (P : Knobs p.g n→Prop) :
    pr (pairW (sketchLaw p n a) unif) (fun x=>
      P (compound p (fun i=>recenterQuery H o l s f S (x.1 i) x.2) u))≤
        (labFee p I)⁻¹*pr (spins p n) P := by
  have hc (x : (I→Knobs p.g n)×Module.Dual F H) :
      pairW (sketchLaw p n a) unif x≤(labFee p I)⁻¹*pairW unif unif x := by
    exact (mul_le_mul_of_nonneg_right (sketch_uniform_cap a hn x.1)
      (unif_law.nz x.2)).trans_eq (by dsimp [pairW]; ring)
  refine (pr_cap hc _).trans_eq ?_
  congr 1
  rw [←mapW_pr,coherent_compound_uniform H o l s f S u hu]

theorem coherent_sketch_failure (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (S : Module.Dual F H→ₗ[F]Vec (Fin n))
    (a : I→Tickets p) (hn : 2*p.r≤n) (P : Knobs p.g n→Prop) (ε : ℝ)
    (hP : pr (spins p n) P≤ε) :
    pr (pairW (sketchLaw p n a) unif) (fun x=>∃ u,weightsAff u ∧
      P (compound p (fun i=>recenterQuery H o l s f S (x.1 i) x.2) u))≤
        num (Vec I)*(labFee p I)⁻¹*ε := by
  classical
  have hw:=pairW_law (sketch_law p n a hn) (unif_law (α:=Module.Dual F H))
  have hp (u : Vec I) :
      pr (pairW (sketchLaw p n a) unif) (fun x=>weightsAff u ∧
        P (compound p (fun i=>recenterQuery H o l s f S (x.1 i) x.2) u))≤
          (labFee p I)⁻¹*ε := by
    by_cases hu : weightsAff u
    · simp only [hu,true_and]
      exact (coherent_sketch_point H o l s f S a hn u hu P).trans
        (mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr (labFee_pos p I).le))
    simp only [hu,false_and,pr_false]
    exact mul_nonneg (inv_nonneg.mpr (labFee_pos p I).le)
      ((pr_nonneg (spins_law p n).nz).trans hP)
  exact (pr_exists_le hw.nz _).trans ((Finset.sum_le_sum fun u _=>hp u).trans_eq
    (by simp only [Finset.sum_const,card_univ,nsmul_eq_mul,num,mul_assoc]))

end
end Lax793645Proofs.Simplifications
