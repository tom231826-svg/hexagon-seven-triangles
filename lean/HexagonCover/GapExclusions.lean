import HexagonCover.GapPatternChains
import HexagonCover.GapForcedPoint
import HexagonCover.SourceGap

/-! Eight fixed-label gap patterns are excluded by actual points in the SAME
central triangle. The remaining sole-E4 case is not excluded by this module. -/
namespace HexagonCover.GapExclusions
open Configuration NormalizedHeavy BoundaryGaps SourceCoordinates
noncomputable section

theorem R_far_last (k : Fin 4) {x : ℝ} (hx : 0  ≤  x) (hx' : x  <  (1:ℝ)/5) :
    1  <  dist GapForcedPoint.R
      (AffineMap.lineMap (vertex (k.castSucc.castSucc+1)) (vertex k.castSucc.castSucc) x) := by
  have hs := TriangleFrame.dist_sq_coordinates GapForcedPoint.R
    (AffineMap.lineMap (vertex (k.castSucc.castSucc+1)) (vertex k.castSucc.castSucc) x)
  have hn := dist_nonneg (x:=GapForcedPoint.R)
    (y:=AffineMap.lineMap (vertex (k.castSucc.castSucc+1)) (vertex k.castSucc.castSucc) x)
  generalize he : dist GapForcedPoint.R
    (AffineMap.lineMap (vertex (k.castSucc.castSucc+1)) (vertex k.castSucc.castSucc) x)=d at hs hn ⊢
  rw [vertex_table] at hs
  fin_cases k
  all_goals
    norm_num [GapForcedPoint.R,AffineMap.lineMap_apply,point] at hs
    ring_nf at hs
    simp only [ExtremeTriangle.halfRoot_sq] at hs
    nlinarith only [hs,hx,hx',hn,sq_nonneg x]

theorem R_far_edge3 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    1  <  dist GapForcedPoint.R (AffineMap.lineMap (vertex 3) (vertex 4) t) := by
  have hs := TriangleFrame.dist_sq_coordinates GapForcedPoint.R
    (AffineMap.lineMap (vertex 3) (vertex 4) t)
  have hn := dist_nonneg (x:=GapForcedPoint.R)
    (y:=AffineMap.lineMap (vertex 3) (vertex 4) t)
  generalize he : dist GapForcedPoint.R (AffineMap.lineMap (vertex 3) (vertex 4) t)=d at hs hn ⊢
  rw [vertex_table] at hs
  norm_num [GapForcedPoint.R,AffineMap.lineMap_apply,point] at hs
  ring_nf at hs
  simp only [ExtremeTriangle.halfRoot_sq] at hs
  have hm := mul_nonneg (sub_nonneg.mpr ht.2) (show 0  ≤  7/5-t by linarith [ht.2])
  nlinarith only [hs,hn,hm]

theorem only_edge4 {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (somegap : ∃i,gap h.cover i) : ∀i,gap h.cover i ↔ i=4 := by
  have hM := GapScale.gap_nine_tenths h somegap
  have hb := GapPatternChains.all_patterns_b0 h somegap
  have hR := GapForcedPoint.same_central h hM hb
  obtain ⟨k,hk,last⟩ := GapScale.last_gap h somegap
  have hshort := GapScale.last_gap_short_upper h k last
  have hheavy := GapChains.heavy_short h
  have no_small : ∀j : Fin 4, k≠j.castSucc := by
    intro j he
    subst k
    have hp := SourceGap.left_endpoint h.cover j.castSucc.castSucc hk
    have hadd : j.castSucc.castSucc+1=j.castSucc.succ := by fin_cases j <;> decide
    have hfar := R_far_last j (x:=a h.cover (j.castSucc.castSucc+1))
      (leftReach h.cover _).positive.le (by rw [hadd]; linarith)
    exact (not_le.mpr hfar) ((rotateConfig config 6).dist_le_one hR hp)
  have hk4 : k=4 := by
    fin_cases k
    · exact (no_small 0 rfl).elim
    · exact (no_small 1 rfl).elim
    · exact (no_small 2 rfl).elim
    · exact (no_small 3 rfl).elim
    · rfl
  have h4 : gap h.cover 4 := by simpa [hk4] using hk
  have h3 : ¬gap h.cover 3 := by
    intro hg
    have hp := SourceGap.right_endpoint h.cover 3 hg
    have hfar := R_far_edge3 ⟨(rightReach h.cover 3).positive.le,(rightReach h.cover 3).lt_one.le⟩
    exact (not_le.mpr hfar) ((rotateConfig config 6).dist_le_one hR hp)
  obtain ⟨S,hS,hpattern⟩ := GapScale.normalized_nine_patterns h somegap
  have h4mem := (hpattern 4).mp h4
  have h3not : (3:Fin 6)∉S := fun hh=>h3 ((hpattern 3).mpr hh)
  have hS4 : S={4} := by
    simp only [ninePatterns,List.mem_cons,List.not_mem_nil,or_false] at hS
    rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num at *
  intro i
  simpa only [hS4,Finset.mem_singleton] using hpattern i

end
end HexagonCover.GapExclusions
