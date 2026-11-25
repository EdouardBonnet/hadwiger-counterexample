/-
Adapted from UnaryRecords (OpenAI, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Apache-2.0). The pruning and Gram argument requires only the exact number
of new key directions, independent of how that property is obtained.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UnaryRecords

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Volley
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]
variable (v w : Volley p n I)

private theorem carried_heavy {T : Type} [Fintype T] {w : Wgt T} {p : T→Prop}
    (x) (hx : onW w p x ≠ 0) : p x :=
  Classical.byContradiction fun h => hx (normW_carried (subW_carried w p) x h)

set_option maxHeartbeats 800000 in
theorem record_hit_of_slots {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (U V : UnitType p n N → Prop) (u : Keys (p:=p) t N)
    (ha : ∀ x, U x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)) ∧ v.keys t x=u)
    (hb : ∀ x, V x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)) ∧ w.keys t x=u)
    {ζ : ℝ}
    (h : ∀ x,U x → ∀ y,V y → v.promised w t m a.sp b.sp x y)
    (hv : planNew a.sp (v.keyPlan t)=kslots p I)
    (hw : planNew b.sp (w.keyPlan t)=kslots p I)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (L : ℝ)
    (hLf : bp (dim (Ledger (v.frozen a.sp t))) ≤ L)
    (hLg : bp (dim (Ledger (w.frozen b.sp t))) ≤ L) :
    hit N * (pr μ U * pr δ V) ≤ pr (pairW μ δ) (fun x => U x.1 ∧ V x.2 ∧
      (rawHoles m).conflict x.1 x.2) +
      (hit N*tau N (kslots p I)*L)*(pr μ U+pr δ V) := by
  classical
  let k := kslots p I
  obtain ⟨x0,hx⟩ :
      ∃ x0 : UnitType p n N,∀ x,U x → (Pin.make (v.frozen a.sp t) x0).agree x := by
    by_cases he : ∃ x,U x
    · obtain ⟨x0,hx0⟩ := he
      exact ⟨x0,fun x hx => key_pin t (ha x0 hx0).1 (ha x hx).1
        ((ha x0 hx0).2.2.trans (ha x hx).2.2.symm)⟩
    exact ⟨0,fun x h => (he ⟨x,h⟩).elim⟩
  let f := Pin.make (v.frozen a.sp t) x0
  obtain ⟨y0,hy⟩ :
      ∃ y0 : UnitType p n N,∀ y,V y → (Pin.make (w.frozen b.sp t) y0).agree y := by
    by_cases he : ∃ y,V y
    · obtain ⟨y0,hy0⟩ := he
      exact ⟨y0,fun y hy => key_pin t (hb y0 hy0).1 (hb y hy).1
        ((hb y0 hy0).2.2.trans (hb y hy).2.2.symm)⟩
    exact ⟨0,fun y h => (he ⟨y,h⟩).elim⟩
  let g := Pin.make (w.frozen b.sp t) y0
  apply prune_pairs μ δ hμ hδ U V (entries g) (entries f)
    (fun x => (rawHoles m).conflict x.1 x.2) (hit N) (tau N k)
    (bp_pos _).le (bp_pos _) _ _
  · intro i j hi hj
    let F := memberC U (entries g) i
    let G := memberC V (entries f) j
    let α := onW μ F
    let β := onW δ G
    change tau N k≤pr μ F at hi
    change tau N k≤pr δ G at hj
    have hL (v : Volley p n I) {a} (h : planNew a (v.keyPlan t)=kslots p I) :
        planRank (v.frozen a t)=planRank a+k := by
      unfold k
      rw [← h]; exact (plan_add_rank a (v.keyPlan t)).symm
    obtain ⟨hα,hF⟩ := in_clear (f:=f) hz hK hμ hA le_sup_left (hL v hv)
      F (fun x h => hx x h.1) hi
    obtain ⟨hβ,hG⟩ := in_clear (f:=g) hz hK hδ hB le_sup_left (hL w hw)
      G (fun x h => hy x h.1) hj
    obtain ⟨x,xX,_⟩ := exists_of_pr_pos hμ.nz (lt_of_lt_of_le (bp_pos _) hi)
    obtain ⟨y,yY,_⟩ := exists_of_pr_pos hδ.nz (lt_of_lt_of_le (bp_pos _) hj)
    have h1 x (h : α x≠0) : F x := carried_heavy _ h
    have h2 y (h : β y≠0) : G y := carried_heavy _ h
    obtain ⟨hr,ht,hL,Q,hZ,hI,hQ,hQ'⟩ := h x xX.1 y yY.1
    have he x' (hs : α x'≠0) y' (hs' : β y'≠0) :
        rowAgree f.sp (actual p x' y') Q ∧
        rowAgree g.sp (actual p y' x') (reciprocal p Q) := by
      have ha := h1 x' hs
      have hb := h2 y' hs'
      exact ⟨rowAgree_step (entries_rows f (hx x' ha.1) (hx x xX.1) (hb.2.trans yY.2.symm)) hQ,
        rowAgree_step (entries_rows g (hy y' hb.1) (hy y yY.1) (ha.2.trans xX.2.symm)) hQ'⟩
    refine (gram_hit Q hα hβ hF hG he hN hT).trans (pr_on_mono (pairW_law hα hβ).nz ?_)
    rintro ⟨x,y⟩ hxy heq
    obtain ⟨_,hx,hX⟩ := ha x (h1 x (left_ne_zero_of_mul hxy)).1
    obtain ⟨_,hy,hY⟩ := hb y (h2 y (right_ne_zero_of_mul hxy)).1
    have he : scalarBlocks p (actual p x y) = scalarBlocks p Q := congrArg Prod.fst heq
    have he' : scalarBlocks p (actual p y x) = scalarBlocks p (reciprocal p Q) := by
      rw [← reciprocal_actual x y]; exact congrArg Prod.snd heq
    apply v.realized_conflicts w m x y hr ht hx hy (hX.trans hY.symm) hL
    · intro i j μ hμ; rw [contract_scalars _ _ he]; exact hZ i j _ hμ
    · intro i j μ hμ; rw [contract_scalars _ _ he']; exact hI i j _ hμ
  · rw [card_space]; exact hLg
  rw [card_space]; exact hLf
end
end Lax793645Proofs.Simplifications
