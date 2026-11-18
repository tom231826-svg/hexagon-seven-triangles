import HexagonCover.HighMNorms
import HexagonCover.HighMNoGap

/-! Actual residual duties for q=21/100. This is a source-exposed extension of
the low-reach source's inequalities to all h≤M<1, separately proved here. -/
namespace HexagonCover.HighMActual
noncomputable section
open TriangleFrame HeavyDepth HighMChart HighMPoints HighMScalar HighMNorms
  SourceCoordinates HexagonCover.Configuration NormalizedHeavy
local notation "h₀" => NICertificate.halfRoot

theorem parameter_bounds {T : UnitTriangle} {M a : ℝ} (w : Witness T M a)
    (hM : h₀≤M) : w.r<7/20 ∧ S w.r<49/40 ∧ 13/49<(inward w.r) 1 := by
  have hM4 : 4/5<M := by linarith [HighMScalar.root_bounds.1]
  have hMM : 3/4≤M^2 := by nlinarith [ExtremeTriangle.halfRoot_sq,ExtremeTriangle.halfRoot_pos]
  have hr : w.r<7/20 := by
    apply w.r_lt.trans
    apply (div_lt_iff₀ (by linarith : 0<2*M-1)).mpr
    nlinarith only [hMM,hM,HighMScalar.root_bounds.1]
  have hS := (box_bounds w.r_pos hr).2.2.2.2.2.2
  have hny : 13/49<(inward w.r) 1 := by
    change 13/49<(1-w.r)/(2*S w.r)
    apply (lt_div_iff₀ (mul_pos (by norm_num) (S_pos w.r))).mpr
    linarith
  exact ⟨hr,hS,hny⟩

theorem coordinates {T : UnitTriangle} {M a k : ℝ} (w : Witness T M a)
    (hM : h₀≤M) (hM1 : M<1) (hk0 : -q≤k) (hk1 : k≤q) :
    1/2<residual w.r w.D k 0 ∧ 0<residual w.r w.D k 1 ∧
      residual w.r w.D k 1<h₀ := by
  have hb := parameter_bounds w hM
  have hn := inward_bounds w.r_pos (by linarith [hb.1])
  have hMh : 3/4≤h₀*M := by
    have hm := mul_le_mul_of_nonneg_left hM ExtremeTriangle.halfRoot_pos.le
    nlinarith only [hm,ExtremeTriangle.halfRoot_sq]
  have hD : 3/4<w.D := hMh.trans_lt w.lower
  have hD0 : 0<w.D := by linarith
  have hDh := w.lt_height (by linarith [HighMScalar.root_bounds.1]) hM1
  have hnx0 : 0<(inward w.r) 0 := ExtremeTriangle.halfRoot_pos.trans hn.1
  have hky := mul_nonneg (show 0≤k+q by linarith) hn.2.2.1.le
  have hkx := mul_nonneg (show 0≤q-k by linarith) hnx0.le
  have hkxn := mul_nonneg (show 0≤k+q by linarith) hnx0.le
  have hxbase : h₀-q/2<(inward w.r) 0+k*(inward w.r) 1 := by
    unfold q at *
    nlinarith only [hky,hn.1,hn.2.2.2]
  have hxD := mul_lt_mul_of_pos_left hxbase hD0
  have hxlo := mul_lt_mul_of_pos_right hD
    (show 0<h₀-q/2 by unfold q; linarith [HighMScalar.root_bounds.1])
  have hx : 1/2<residual w.r w.D k 0 := by
    rw [residual_x]
    unfold q at hxD hxlo
    nlinarith only [hxD,hxlo,HighMScalar.root_bounds.1]
  have hybase : 0<(inward w.r) 1-k*(inward w.r) 0 := by
    unfold q at hkx
    nlinarith only [hb.2.2,hkx,hn.2.1]
  have hyupper : (inward w.r) 1-k*(inward w.r) 0<3/4 := by
    unfold q at hkxn
    nlinarith only [hkxn,hn.2.1,hn.2.2.2]
  refine ⟨hx,?_,?_⟩
  · rw [residual_y]
    exact mul_pos hD0 hybase
  · rw [residual_y]
    nlinarith only [mul_lt_mul_of_pos_left hyupper hD0,hDh,hD0]

theorem ahat_lt_half {T : UnitTriangle} {M a : ℝ} (w : Witness T M a)
    (hM : h₀≤M) : ahat w.D w.r<1/2 := by
  have hr := (parameter_bounds w hM).1
  have hM0 : 0<M := by linarith [HighMScalar.root_bounds.1]
  have hD0 : 0<w.D := (mul_pos ExtremeTriangle.halfRoot_pos hM0).trans w.lower
  have hDS := mul_le_mul_of_nonneg_left (S_ge_one w.r_pos.le) hD0.le
  have hdiv : M<w.D*S w.r/h₀ := by
    apply (lt_div_iff₀ ExtremeTriangle.halfRoot_pos).mpr
    nlinarith only [hDS,w.lower]
  unfold ahat
  linarith [HighMScalar.root_bounds.1]

theorem zero_hat_far {T : UnitTriangle} {M a k : ℝ} (w : Witness T M a)
    (hM : h₀≤M) (hk : k=-q ∨ k=q) :
    1<dist (residual w.r w.D k) (Xhat w.D w.r)^2 := by
  have hp := X_positive hM w.lower w.r_pos (parameter_bounds w hM).1
  have hid := zero_minus_identity w.D w.r
  have hm : 1<dist (residual w.r w.D (-q)) (Xhat w.D w.r)^2 := by linarith
  rcases hk with rfl | rfl
  · exact hm
  have hn := inward_bounds w.r_pos (by linarith [(parameter_bounds w hM).1])
  have hhat := ahat_lt_half w hM
  have ht : dotp (tangent w.r) (Xhat w.D w.r)<0 := by
    have hp0 := mul_neg_of_pos_of_neg hn.2.2.1 (show ahat w.D w.r-1/2<0 by linarith)
    have hp1 := mul_pos (ExtremeTriangle.halfRoot_pos.trans hn.1) ExtremeTriangle.halfRoot_pos
    dsimp [tangent,Xhat,dotp]
    linarith only [hp0,hp1]
  have hD0 : 0<w.D := (mul_pos ExtremeTriangle.halfRoot_pos (by linarith [HighMScalar.root_bounds.1])).trans w.lower
  have hd := sign_difference w.r w.D q (Xhat w.D w.r)
  have hprod : 0 < -4*q*w.D*dotp (tangent w.r) (Xhat w.D w.r) := by
    have hq : 0<q := by norm_num [q]
    exact mul_pos_of_neg_of_neg (by nlinarith [mul_pos hq hD0]) ht
  linarith only [hd,hm,hprod]

theorem fourth_virtual_far {T : UnitTriangle} {M a k : ℝ} (w : Witness T M a)
    (hM : h₀≤M) (hM1 : M<1) (hk : k=-q ∨ k=q) :
    1<dist (residual w.r w.D k) (V4 M)^2 := by
  have hp := X4_positive hM hM1 w.lower w.r_pos.le w.r_lt.le
  have hid := fourth_plus_identity w.D M w.r
  have hm : 1<dist (residual w.r w.D q) (V4 M)^2 := by linarith
  rcases hk with rfl | rfl
  · have hn := inward_bounds w.r_pos (by linarith [(parameter_bounds w hM).1])
    have ht : 0<dotp (tangent w.r) (V4 M) := by
      have hp0 := mul_pos hn.2.2.1 (show 0<M-1/2 by linarith [HighMScalar.root_bounds.1])
      have hp1 := mul_pos (ExtremeTriangle.halfRoot_pos.trans hn.1) ExtremeTriangle.halfRoot_pos
      dsimp [tangent,V4,dotp]
      nlinarith only [hp0,hp1]
    have hD0 : 0<w.D := (mul_pos ExtremeTriangle.halfRoot_pos (by linarith [HighMScalar.root_bounds.1])).trans w.lower
    have hd := sign_difference w.r w.D q (V4 M)
    have hprod : -4*q*w.D*dotp (tangent w.r) (V4 M)<0 := by
      have hq : 0<q := by norm_num [q]
      exact mul_neg_of_neg_of_pos (by nlinarith [mul_pos hq hD0]) ht
    linarith only [hd,hm,hprod]
  · exact hm

theorem same_central {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (hM : h₀≤M h)
    (w : Witness (rotateConfig config 5) (M h) (a h.cover 5))
    {k : ℝ} (hk : k=-q ∨ k=q) : residual w.r w.D k∈(rotateConfig config 6).region := by
  have hM1 := (structure_bounds h).2.2.2.2.1
  have hk0 : -q≤k := by rcases hk with rfl|rfl <;> norm_num [q]
  have hk1 : k≤q := by rcases hk with rfl|rfl <;> norm_num [q]
  have hc := coordinates w hM hM1 hk0 hk1
  have hp : residual w.r w.D k∈interior (Hexagon 1) := by
    have hm := first_quadrant_interior hc.1 hc.2.1 hc.2.2
      (residual_facet w (by linarith [HighMScalar.root_bounds.1]) hM1
        (by unfold q at hk0; linarith) (by unfold q at hk1; linarith))
    have he : point (residual w.r w.D k 0) (residual w.r w.D k 1)=residual w.r w.D k := by
      ext i
      fin_cases i <;> rfl
    rwa [he] at hm
  apply HighMResidual.supporting_line_forced (covered h.cover) hp w.unit
    (residual_line w.r w.D k) _ w.halfplane
  intro i hi5
  by_cases hi0 : i=0
  · subst i
    apply HighMResidual.exclude_by_actual_point _ (zero_endpoint h)
    have hhat := zero_hat_far w hM hk
    have ha := NoGapChain.a_strictMono h nogaps (show (1:Fin 6)<5 by decide)
    have hg := le_of_not_gt (nogaps 0)
    change 1≤b h.cover 0+a h.cover 1 at hg
    have hshort := w.short
    change a h.cover 5≤ahat w.D w.r at hshort
    have hcomp := left_comparison (residual w.r w.D k)
      (show 1/2-b h.cover 0≤ahat w.D w.r-1/2 by linarith)
      (show ahat w.D w.r-1/2≤residual w.r w.D k 0 by linarith [ahat_lt_half w hM])
      (y:=h₀)
    exact hhat.trans_le hcomp
  by_cases hi4 : i=4
  · subst i
    apply HighMResidual.exclude_by_actual_point _ (fourth_left_endpoint h)
    have hvirtual := fourth_virtual_far w hM hM1 hk
    have ha := HighMNoGap.fourth_short_lower h nogaps
    have hcomp := left_comparison (residual w.r w.D k)
      (show 1/2-a h.cover 4≤M h-1/2 by linarith)
      (show M h-1/2≤residual w.r w.D k 0 by linarith [hc.1]) (y:=-h₀)
    exact hvirtual.trans_le hcomp
  apply HighMResidual.exclude_by_actual_point _ (anchors h.cover i)
  apply far_of_x
  fin_cases i
  all_goals try exact (hi0 rfl).elim
  all_goals try exact (hi4 rfl).elim
  all_goals try exact (hi5 rfl).elim
  all_goals norm_num [vertex_table]
  all_goals linarith [hc.1]

end
end HexagonCover.HighMActual

#print axioms HexagonCover.HighMActual.same_central
