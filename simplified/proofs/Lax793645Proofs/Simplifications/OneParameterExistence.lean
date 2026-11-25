import Lax793645Proofs.Simplifications.OneCollisionCalendar
import Lax793645Proofs.Simplifications.OnePreparationCalendar
import Lax793645Proofs.Simplifications.OneInitialPreparation
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ParameterExistence

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Matrix PreparationParameters
open scoped BigOperators Topology
noncomputable section
namespace OneParameters

structure Complete (p:Shape) (M:ℕ) (b:PreparationParameters) (s0:ℕ):Prop
    extends OneAnalyticParameters p M b s0 where
  initial:∀ᶠ n:ℕ in atTop,∀ (m:Mixer p n) (w:Wgt (OneUnit p n (M*n))),
    OneNascent b m w → carried w (fun x=>(oneRawHoles m).unit (x true,x false)) →
    ∃ s:OneLeafMixture p n (M*n),OneEntered b m w s
  mixerRoom:s0≤p.J

structure Ribbon (g : ℕ) (b:PreparationParameters):Prop where
  life:OnePreparationAllows b
  hd:b.D=8000
  mercury:b.L=bp 1000
  rain:(b.D:ℝ)+b.ζ≤((b.ζ/6)-(b.ζ/6)/4)*b.e
  hk:b.k≤b.d
  beam:b.spJoint+1≤0.49*b.k
  dul:3*onePreparationCover b+1≤b.u
  reserve:10*oneScalarBudget ⟨g,0,1,0,0,0⟩ (onePreparationPins b)+1000≤b.B
  dust:2*b.ζ≤0.004 ∧ 2*b.ζ*112≤0.004

private theorem floor_supply (x y:ℝ) (hy:0<y):∃ k:ℕ,x≤y*k := by
  obtain ⟨k,hk⟩:=((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (x/y))).exists
  exact ⟨k,by rw [mul_comm]; exact (div_le_iff₀ hy).mp hk⟩

set_option maxHeartbeats 400000 in
theorem seed_ribbon:∃ (g : ℕ) (b:PreparationParameters),
    Ribbon g b ∧ Odd g ∧ 4*b.e+20000<g := by
  let ζ:ℝ:=1/(1000*112)
  have hζ:0<ζ ∧ ζ≤1/1000:=by norm_num [ζ]
  have hgap:0<(ζ/6)-(ζ/6)/4:=by linarith only [hζ.1]
  let D:ℕ:=8000
  obtain ⟨e,he⟩:=floor_supply ((D:ℝ)+ζ) _ hgap
  obtain ⟨k,hk⟩:=floor_supply ((D:ℝ)+2) 0.49 (by norm_num)
  let d:=(2*e+2)*4*k
  let u:=10*(e+d+1)
  obtain ⟨s,hs⟩:=floor_supply ((D:ℝ)+e+2+u+ζ) _ hgap
  let g:=2*(2*e+10000)+1
  let b:PreparationParameters:=⟨D,bp 1000,d,e,s,u,k,ζ,
    10*(10*oneScalarBudget ⟨g,0,1,0,0,0⟩ (e+s)+10000*g+1)⟩
  refine ⟨g,b,⟨⟨hζ.1,hζ.2.trans_lt (by norm_num),(bp_pos _).le,hs⟩,rfl,rfl,he,?_,?_,?_,?_,?_⟩,
    ⟨2*e+10000,rfl⟩,by dsimp only [b,g]; omega⟩
  · change k≤d; unfold d; nlinarith
  · change (D:ℝ)+1+1≤0.49*k
    linarith only [hk]
  · change 3*(2*d)+1≤u; unfold u; omega
  · change 10*oneScalarBudget _ (e+s)+1000≤10*(_+10000*g+1)
    have hg:3≤g:=by dsimp only [g]; omega
    omega
  change 2*ζ≤_ ∧ 2*ζ*112≤_
  norm_num [ζ]

private def layout (g b j J r:ℕ):Shape:=⟨g,b,j,J,r,1000*r⟩

private def roomCost (p:Shape) (K t:ℕ):ℕ:=
  let f:=2*(K+t)
  oneGradientRank p+(f+K)+jointCompressionRank p f (2*f+(f+K))+5*K+6*f+2

private theorem lanes_need (g K b j J:ℕ):
    ∀ᶠ r:ℕ in atTop,∀ t≤28,oneRealizationRoom (layout g b j J r) K t := by
  let c:=roomCost (layout g b j J 0) K 28
  filter_upwards [eventually_ge_atTop c] with r hr t ht
  change roomCost (layout g b j J r) K t≤1000*r
  have hmono:roomCost (layout g b j J r) K t≤roomCost (layout g b j J r) K 28:=by
    dsimp only [roomCost,jointCompressionRank,drow,dbits]
    gcongr
  have hcost:roomCost (layout g b j J r) K 28=c+30*r:=by
    dsimp only [c,roomCost,oneGradientRank,jointCompressionRank,drow,dbits,psize,nbBlock,ncComp,layout]
    ring
  rw [hcost] at hmono
  omega

private theorem exact_altitude_need (g K b j J : ℕ) (hg : 4*K+20000<g) :
    ∀ᶠ r : ℕ in atTop,let p:=layout g b j J r;
      4*oneScreenRank p K+2*K*p.r<p.g*p.r := by
  filter_upwards [eventually_ge_atTop (J*K+1)] with r hr
  unfold oneScreenRank layout
  dsimp only
  have hdeg : tagDegree g=2 := by simp [tagDegree,CycleGeometry.degree]; omega
  rw [hdeg]
  nlinarith only [hr,hg]

private theorem labels_large (j B g : ℕ) (hg : 3≤g) :
    ∃ b:ℕ,(B:ℝ)<bp ((b:ℝ)-2*j) ∧ 3*B < Fintype.card (Label b) := by
  classical
  obtain ⟨b,hb⟩ := ((bp_poly_dom_nat (a:=1) zero_lt_one
    (100*g*(B+1:ℝ)*bp (2*j)) 0)).exists
  have he : 100*g*(B+1:ℝ)*bp (2*j)< bp (b:ℝ) := by simpa using hb
  have hb' : (B:ℝ)<bp ((b:ℝ)-2*j) := by
    rw [bp_sub,lt_div_iff₀ (bp_pos _)]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by
      have hh : 3≤(g:ℝ) := by exact_mod_cast hg
      nlinarith [(Nat.cast_nonneg B : 0≤(B:ℝ))]) (bp_pos _).le) he
  have hb'' : 3*B < Fintype.card (Label b) := by
    have hs : 1 ≤ bp (2*j) := by rw [←bp_zero]; exact bp_le (by positivity)
    have hh : Fintype.card (Label b)=2^b := by simp [Label,F]
    have heq : 3*(B:ℝ) < bp b := by
      have hh : 3≤(g:ℝ):=by exact_mod_cast hg
      refine lt_of_le_of_lt ?_ he
      have hz : 100*g*(B+1:ℝ) ≤ 100*g*(B+1:ℝ)*bp (2*j) := by
        exact le_mul_of_one_le_right (by positivity) hs
      nlinarith [(Nat.cast_nonneg B :0≤(B:ℝ))]
    rw [hh]; rw [bp_nat] at heq; exact_mod_cast heq
  exact ⟨b,hb',hb''⟩

private theorem late_altitude_need (g K b j J : ℕ) (hg : 20000<g) :
    ∀ᶠ r : ℕ in atTop,let p:=layout g b j J r;
      4*oneScreenRank p K<p.g*p.r := by
  filter_upwards [eventually_ge_atTop (J*K+1)] with r hr
  unfold oneScreenRank layout
  dsimp only
  have hdeg : tagDegree g=2 := by simp [tagDegree,CycleGeometry.degree]; omega
  rw [hdeg]
  nlinarith only [hr,hg]

set_option maxHeartbeats 600000 in
theorem exists_parameters:∃ (p:Shape) (b:PreparationParameters) (M s0:ℕ),
    Complete p M b s0 ∧ 4*b.e+20000<p.g ∧ b.D=8000 ∧ b.L=bp 1000 := by
  obtain ⟨g,t,ht,hodd,hlarge⟩:=seed_ribbon
  let K:=onePreparationPins t
  have hg:3≤g:=by omega
  let j:ℕ:=1
  obtain ⟨b,hb,hb'⟩:=labels_large j t.B g hg
  let C:=profileA (layout g b j 0 0) K
  let s0:=4*C+1
  let J:=100*(s0+K^2+1)+1
  have hJ:1≤J ∧ s0≤J:=by unfold J; omega
  have hgleam:bp (-((J-s0:ℕ):ℝ))*bp s0<glintRate K:=by
    rw [←bp_add]; apply bp_lt
    have hh:K^2+4+s0≤J-s0:=by unfold J; omega
    have hi:((K^2:ℕ):ℝ)+4+(s0:ℝ)≤((J-s0:ℕ):ℝ):=by exact_mod_cast hh
    linarith only [hi]
  obtain ⟨h0,hcal⟩:=Filter.eventually_atTop.mp
    (one_preparation_calendar t g ht.life ht.hk ht.beam ht.dul)
  obtain ⟨r,hr,hexact,hlate,hr1,hr0⟩:=((lanes_need g K b j J).and
    ((exact_altitude_need g t.e b j J hlarge).and
      ((late_altitude_need g K b j J (by omega)).and
        ((eventually_ge_atTop (1:ℕ)).and (eventually_ge_atTop h0))))).exists
  let p:=layout g b j J r
  have hj:1≤p.j:=by change 1≤j; omega
  have hD:0<t.D:=by rw [ht.hd]; norm_num
  have hplant:=hcal p.h (show h0≤1000*r by omega) p rfl rfl hodd hg hj hr1 hb
    hexact
  obtain ⟨M,hp,hM,hcol,hinit⟩:=(hplant.and ((eventually_ge_atTop (4:ℕ)).and
    ((one_collision_calendar p K).and (one_entered_calendar t p hD ht.life ht.rain)))).exists
  have hprofiles:2*C<s0:=by unfold s0; omega
  refine ⟨p,t,M,s0,⟨⟨hp,⟨hp.hM,hodd,hj,hr1,hprofiles,hgleam⟩,hM,rfl,hJ.1,
    ht.reserve,hb',hlate,?_⟩,hinit,hJ.2⟩,hlarge,ht.hd,ht.mercury⟩
  filter_upwards [hcol,eventually_ge_atTop (2*r)] with n hn hnR
  refine ⟨hr1,hnR,hodd,hr,by linarith only [ht.life.pos],ht.dust.1,?_,hn.1,hn.2.1,hn.2.2⟩
  have hslots:oneMaxSlots p≤112:=by
    unfold oneMaxSlots tagDegree CycleGeometry.degree
    have hh:=min_le_left 2 (p.g-1)
    omega
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hslots)
    (by linarith only [ht.life.pos])).trans ht.dust.2

end OneParameters
end
end Lax793645Proofs.Simplifications
