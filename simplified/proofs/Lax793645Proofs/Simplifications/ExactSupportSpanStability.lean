import Lax793645Proofs.Simplifications.ExactStatusPredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function Finset Matrix LinearMap Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
theorem whole_rhyme_form {d : ℕ} (f : Whole d→ₗ[F]F) :
    ∃ a : RhymeSet d,∀ x,a.read 0 x=f x := by
  let g:=f.comp ((LinearMap.inl F (Par d) F).comp (LinearMap.inr F F (Cell d)))
  obtain ⟨u,hu⟩:=dotL_surj g
  let b:=f (0,1)
  let h:=f ((1,0),0)
  refine ⟨⟨b,u,b+h,0⟩,?_⟩
  rintro ⟨⟨x,y⟩,z⟩
  have he : (((x,y),z):Whole d)=x • ((1,0),0)+((0,y),0)+z • (0,1) := by
    ext <;> simp
  have hy : f ((0,y),0)=dotProduct u y := LinearMap.congr_fun hu y
  have hf : f ((x,y),z)=x*h+dotProduct u y+z*b := by
    rw [he,map_add,map_add,map_smul,map_smul,hy]
    rfl
  rw [hf]
  change b*z+dotProduct u y+(b+(b+h))*x+0*0=x*h+dotProduct u y+z*b
  rw [←add_assoc b b h,char_two,zero_add]
  ring

theorem signal_rhyme_form {d e : ℕ} (f : Signal d e→ₗ[F]F) :
    ∃ a : RhymeSet d,∃ b : RhymeSet e,
      ∀ x,f x=a.read x.1 x.2.1+b.read x.1 x.2.2 := by
  let fA:=f.comp ((LinearMap.inr F F (Whole d×Whole e)).comp
    (LinearMap.inl F (Whole d) (Whole e)))
  let fB:=f.comp ((LinearMap.inr F F (Whole d×Whole e)).comp
    (LinearMap.inr F (Whole d) (Whole e)))
  obtain ⟨a,ha⟩:=whole_rhyme_form fA
  obtain ⟨b,hb⟩:=whole_rhyme_form fB
  let γ:=f (1,0)
  refine ⟨{a with gamma:=γ},{b with gamma:=0},?_⟩
  rintro ⟨q,x,y⟩
  have he : ((q,x,y):Signal d e)=q • (1,0)+(0,x,0)+(0,0,y) := by
    ext <;> simp
  calc
    f (q,x,y)=q*γ+fA x+fB y := by
      rw [he,map_add,map_add,map_smul]
      rfl
    _=({a with gamma:=γ}:RhymeSet d).read q x+
        ({b with gamma:=0}:RhymeSet e).read q y := by
      rw [←ha,←hb]
      simp only [RhymeSet.read,mul_zero,add_zero]
      ring

variable {p : Shape} {r : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}

def StatusLabelContinuation (u : Terrain p r) (s : Gazette p r d) (B : ℕ) : Prop :=
  ∀ i E,E.card≤B→∀ a f,ExactStatusPrediction u s i E a f→
    ExactStatusPrediction u s i ∅ a f

theorem circlet_positive_cell (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (x : Zodiac p) (hx : x.common) (i : Grid) (v : Touch p d e i)
    (h : 0<circlet u s t x i v) :
    ∃ c,0<u x.l x.q c ∧ 0<s i.1 (x.aspect true) c v.1 ∧
      0<t i.2 (x.aspect false) c v.2 := by
  have hex : ∃ c,0<u x.l x.q c*(s i.1 (x.aspect true) c v.1*
      t i.2 (x.aspect false) c v.2) := by
    by_contra! hn
    change 0<∑ c : Fin r,u x.l x.q c*(s i.1 (x.aspect true) c v.1*
      t i.2 (x.aspect false) c v.2) at h
    exact (not_le_of_gt h) (Finset.sum_nonpos (fun c _=>hn c))
  obtain ⟨c,hc⟩:=hex
  have hleft:=(hs.law i.1 _ (hx true) c).nz v.1
  have hright:=(ht.law i.2 _ (hx false) c).nz v.2
  have hprod:=pos_of_mul_pos_right hc ((hu.1 _ _).nz c)
  exact ⟨c,pos_of_mul_pos_left hc (mul_nonneg hleft hright),
    pos_of_mul_pos_left hprod hright,pos_of_mul_pos_right hprod hleft⟩

/-- Exact continuation of unary support relations makes edge spans
invariant under the permitted label deletions. -/
theorem status_band_stable (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η) (hη : 0<η) (hg : 3≤p.g)
    (B : ℕ) (hB : B<Fintype.card (Label p.b))
    (hleft : StatusLabelContinuation u s B) (hright : StatusLabelContinuation u t B)
    (S : Straps (Label p.b)) (hS : ∀ side,(S side).card≤B) (i : Grid) :
    (stellar u s t η ⊥ ⊥ i).band S=(stellar u s t η ⊥ ⊥ i).band ⊥ := by
  classical
  let C:=stellar u s t η ⊥ ⊥ i
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨v,hv,rfl⟩
    exact C.band_write ⊥ (C.zone_smaller bot_le _ hv)
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (C.band S) (C.writes v)).mp
  intro f hf
  have hf' := (Submodule.mem_dualAnnihilator f).mp hf
  obtain ⟨a,b,hab⟩:=signal_rhyme_form f
  have hrel (x y : Appearance p) (hx : x.s∉S true) (hy : y.s∉S false)
      (hax : x.apt) (hay : y.apt) (hl : x.l=y.l) (hq : x.q=y.q)
      (c : Fin r) (hc : 0<u x.l x.q c)
      (z : Magazine p (d i.1)) (w : Magazine p (e i.2))
      (hz : 0<s i.1 x c z) (hw : 0<t i.2 y c w) : a.soot x z=b.soot y w := by
    let X:=amends p x y
    have he : X.aspect false=y:=amendsB x y hl hq
    have hcommon : X.common := by
      intro side
      cases side
      · rw [he]; exact hay
      exact hax
    have hpos : 0<circlet u s t X i (z,w) := by
      have hnonneg (j : Fin r) : 0≤u X.l X.q j*
          (s i.1 (X.aspect true) j z*t i.2 (X.aspect false) j w) :=
        mul_nonneg ((hu.1 _ _).nz j) (mul_nonneg ((hs.law _ _ (hcommon true) j).nz z)
          ((ht.law _ _ (hcommon false) j).nz w))
      apply (mul_pos hc (mul_pos hz (show 0<t i.2 (X.aspect false) c w by rw [he]; exact hw))).trans_le
      exact weight_le_tot hnonneg c
    have hfit := (circlet_state u s t hu hs ht X hcommon i).2
    have hfit' : (X.aspect true).fitsink z ∧ (X.aspect false).fitsink w :=
      not_not.mp (fun h=>hpos.ne' (hfit (z,w) h))
    have hzone : C.zone S (X,z,w) := by
      refine ⟨⟨by simp,by simp,hcommon,hfit'.1,hfit'.2,
        (hgap X hcommon i (z,w)).resolve_left hpos.ne'⟩,?_⟩
      intro side
      cases side
      · exact hy
      exact hx
    have hzero:=hf' _ (C.band_write S hzone)
    rw [hab] at hzero
    change a.read x.q z.2+b.read x.q w.2=0 at hzero
    change a.read x.q z.2=b.read y.q w.2
    rw [←hq]
    exact add_right_cancel (hzero.trans (char_two _).symm)
  obtain ⟨φ,hφ,hφ'⟩:=exact_status_predictors hs.law ht.law i (S true) (S false)
    ((hS true).trans_lt hB) ((hS false).trans_lt hB) hg a b hrel
  have hφall:=hleft i.1 (S true) (hS true) a φ hφ
  have hφall':=hright i.2 (S false) (hS false) b φ hφ'
  have hp : 0<circlet u s t v.1 i v.2:=hη.trans_le hv.1.2.2.2.2.2
  obtain ⟨c,hc,hcA,hcB⟩:=circlet_positive_cell hu hs ht v.1 hv.1.2.2.1 i v.2 hp
  have ha:=hφall (v.1.aspect true) (by simp) (hv.1.2.2.1 true) c hc v.2.1 hcA
  have hb:=hφall' (v.1.aspect false) (by simp) (hv.1.2.2.1 false) c hc v.2.2 hcB
  rw [hab]
  change a.soot (v.1.aspect true) v.2.1+b.soot (v.1.aspect false) v.2.2=0
  rw [ha,hb]
  exact char_two _

end
end Lax793645Proofs.Simplifications
