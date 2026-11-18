import HexagonCover.CentralAxis
import HexagonCover.GapPatternChains

/-! An actual positive edge4 gap forces the same central triangle to contain
the full closed axis interval in its interior. Other gaps need not be excluded. -/
namespace HexagonCover.SoleGapAxis
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates

theorem actual_axis {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (gap4 : BoundaryGaps.gap h.cover 4) :
    ∀x∈Set.Icc (0:ℝ) (47/60),point x 0∈interior (rotateConfig config 6).region := by
  have somegap : ∃i,BoundaryGaps.gap h.cover i := ⟨4,gap4⟩
  have hM := GapScale.gap_nine_tenths h somegap
  have hb0 := GapPatternChains.all_patterns_b0 h somegap
  have hshort := GapChains.heavy_short h
  have ha1 : a h.cover 5 < 1/5 := by linarith
  exact CentralAxis.axis_of_points _ (leftReach h.cover 5).positive.le ha1
    (CentralAxis.source_origin_interior h) (GapForcedPoint.same_central h hM hb0)
    (CentralAxis.source_P_mem h gap4)

theorem quarter_mem_interior {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (gap4 : BoundaryGaps.gap h.cover 4) :
    point (1/4) 0∈interior (rotateConfig config 6).region :=
  actual_axis h gap4 (1/4) (by norm_num)

theorem point761_mem_interior {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (gap4 : BoundaryGaps.gap h.cover 4) :
    point (761/1000) 0∈interior (rotateConfig config 6).region :=
  actual_axis h gap4 (761/1000) (by norm_num)

end
end HexagonCover.SoleGapAxis
