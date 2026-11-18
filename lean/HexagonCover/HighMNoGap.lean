import HexagonCover.NoGapChain
import HexagonCover.SourceCoordinates

/-! Source-exposed high-M prerequisites. Every reach and the central disk
refer to the same normalized configuration. We use the smaller guaranteed
disk rho(1-M); no maximization over a different central placement is involved. -/
namespace HexagonCover.HighMNoGap
noncomputable section
open HexagonCover.Configuration NormalizedHeavy
local notation "h₀" => NICertificate.halfRoot

theorem short_lt_two_complement {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    a h.cover 5 < 2*(1-M h) := by
  have hs := structure_bounds h
  have hM0 : 0<M h := by linarith [hs.2.2.2.1]
  have hM1 : M h<1 := hs.2.2.2.2.1
  have ha0 := (leftReach h.cover 5).positive
  have hexit := ReachEndpoints.actual_exit_constraint h.cover 5
  change (a h.cover 5)^2+a h.cover 5*M h+(M h)^2≤1 at hexit
  by_contra hn
  have ha : 2*(1-M h)≤a h.cover 5 := le_of_not_gt hn
  have hp := mul_nonneg (show 0≤a h.cover 5-2*(1-M h) by linarith)
    (show 0≤a h.cover 5+2*(1-M h)+M h by linarith)
  nlinarith only [hexit,hp,sq_pos_of_pos (show 0<1-M h by linarith)]

theorem first_long_lower {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) : 2*M h-1 < b h.cover 0 := by
  have ha := NoGapChain.a_strictMono h nogaps (show (1:Fin 6)<5 by decide)
  have hs := short_lt_two_complement h
  have hg := le_of_not_gt (nogaps 0)
  change 1≤b h.cover 0+a h.cover 1 at hg
  linarith

theorem fourth_short_lower {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) : 1-M h<a h.cover 4 := by
  have ha := NoGapChain.a_strictMono h nogaps (show (0:Fin 6)<4 by decide)
  have hz := ((structure_bounds h).1 0).trans (min_le_left _ _)
  linarith

theorem same_central_disk {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    Metric.closedBall 0 (CommonReach.rho (1-M h)) ⊆
      (SourceCoordinates.rotateConfig config 6).region := by
  have hs := structure_bounds h
  exact SourceCoordinates.central_disk
    (CentralDisk.actual_central_disk_of_reach_lower h.cover
      (by linarith [hs.2.2.2.2.1]) (by linarith [hs.2.2.2.1]) hs.1)

theorem rho_complement_identity (M : ℝ) :
    2*CommonReach.rho (1-M)=M*(1-M)+(CommonReach.rho (1-M))^2 := by
  have hp : 0≤1-(1-M)+(1-M)^2 := by nlinarith [sq_nonneg (M-1/2)]
  have hs := Real.sq_sqrt hp
  unfold CommonReach.rho CommonReach.radiusSq
  nlinarith only [hs]

theorem depth_disk_strict {M D : ℝ} (hM : h₀≤M) (hM1 : M<1)
    (hD : h₀*M<D) : h₀<D+2*CommonReach.rho (1-M) := by
  have hm := mul_le_mul_of_nonneg_right hM (by linarith : 0≤1-M)
  have hr := rho_complement_identity M
  nlinarith only [hD,hm,hr,sq_nonneg (CommonReach.rho (1-M))]

end
end HexagonCover.HighMNoGap

#print axioms HexagonCover.HighMNoGap.short_lt_two_complement
#print axioms HexagonCover.HighMNoGap.first_long_lower
#print axioms HexagonCover.HighMNoGap.fourth_short_lower
#print axioms HexagonCover.HighMNoGap.same_central_disk
#print axioms HexagonCover.HighMNoGap.depth_disk_strict
