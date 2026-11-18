import HexagonCover.E4Outside
import HexagonCover.E4InsideOwners
import HexagonCover.HeavyDepthTransport

/-! Source-exposed actual T4 contact points: interior and exclusion from the
other five closed outer pieces. All duties refer to the same configuration. -/
namespace HexagonCover.E4T4Points
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def positivePoint (v : ℝ) : Plane := point (3*v/2) (-h₀*v)
def midpoint (v : ℝ) : Plane := point (1/2) (-h₀*v)

theorem positive_interior {v : ℝ} (hv : 0<v) (hv1 : v<1/2) :
    positivePoint v∈interior (Hexagon 1) := by
  have hb := (convex_hexagon 1) (hexVertex_mem 1 0) (hexVertex_mem 1 5)
    (a:=1/2) (b:=1/2) (by norm_num) (by norm_num) (by norm_num)
  have hm := (convex_hexagon 1).combo_interior_self_mem_interior
    (zero_mem_interior_hexagon (by norm_num)) hb
    (a:=1-2*v) (b:=2*v) (by linarith) (by linarith) (by ring)
  have he : (1-2*v) • (0:Plane)+(2*v) •
      ((1/2:ℝ) • hexVertex 1 0+(1/2:ℝ) • hexVertex 1 5)=positivePoint v := by
    ext i
    fin_cases i <;> simp [positivePoint,hexVertex,NICertificate.halfRoot] <;> ring
  exact he ▸ hm

theorem midpoint_interior {v : ℝ} (hv : 0<v) (hv1 : v<1) :
    midpoint v∈interior (Hexagon 1) := by
  have hz := (convex_hexagon 1).combo_interior_self_mem_interior
    (zero_mem_interior_hexagon (by norm_num)) (hexVertex_mem 1 0)
    (a:=1/2) (b:=1/2) (by norm_num) (by norm_num) (by norm_num)
  have hm := (convex_hexagon 1).combo_interior_self_mem_interior hz
    (hexVertex_mem 1 5) (a:=1-v) (b:=v) (by linarith) hv.le (by ring)
  have he : (1-v) • ((1/2:ℝ) • (0:Plane)+(1/2:ℝ) • hexVertex 1 0)+
      v • hexVertex 1 5=midpoint v := by
    ext i
    fin_cases i <;> simp [midpoint,hexVertex,NICertificate.halfRoot] <;> ring
  exact he ▸ hm

theorem positive_anchor_far {v : ℝ} (hv : 0<v) (i : Fin 6)
    (hi : i=1 ∨ i=2 ∨ i=3) : 1 < dist (positivePoint v) (vertex i)^2 := by
  rcases hi with rfl | rfl | rfl
  all_goals norm_num [positivePoint,vertex_table,dist_point_sq]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals nlinarith [sq_pos_of_pos hv]

theorem positive_zero_far {v b : ℝ} (hv : 0<v) (hb : 1-v<b) :
    1<dist (positivePoint v) (point (1/2-b) h₀)^2 := by
  rw [positivePoint,dist_point_sq]
  have hx : 1/2+v/2 < 3*v/2-(1/2-b) := by linarith
  have he : (3*v/2-(1/2-b))^2+(1/2+v/2)^2 * (-1) > 0 := by
    nlinarith only [hx,hv,sq_nonneg (3*v/2-(1/2-b)-(1/2+v/2))]
  ring_nf at *
  simp only [ExtremeTriangle.halfRoot_sq] at *
  nlinarith only [he,hv,sq_nonneg v]

theorem actual_positive_others {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    {v : ℝ} (hv : a h.cover 4<v) (hv1 : v<a h.cover 5)
    (i : Fin 6) (hi : i≠4) :
    positivePoint v∉(rotateConfig config i.castSucc).region := by
  have ha4 : 0<a h.cover 4 := (leftReach h.cover 4).positive
  have hv0 : 0<v := lt_trans ha4 hv
  have hab := E4InsideCentral.actual_a_bounds h sole
  fin_cases i
  · apply E4Outside.exclude_far _ (GapForcedPoint.zero_endpoint h)
    apply positive_zero_far hv0
    have hm := SoleGapArea.a_strictMono h sole (show (1:Fin 5)<4 by decide)
    have hg := le_of_not_gt (SoleGapArea.no_prefix_gap h sole 0)
    change 1≤b h.cover 0+a h.cover 1 at hg
    change a h.cover 1<a h.cover 4 at hm
    linarith
  · exact E4Outside.exclude_far _ (anchors h.cover 1) (positive_anchor_far hv0 1 (by simp))
  · exact E4Outside.exclude_far _ (anchors h.cover 2) (positive_anchor_far hv0 2 (by simp))
  · exact E4Outside.exclude_far _ (anchors h.cover 3) (positive_anchor_far hv0 3 (by simp))
  · exact (hi rfl).elim
  · intro hp
    have hn := SourceCoordinates.separation (config:=config) 5
      (structure_bounds h).2.2.2.2.2 (positivePoint v) hp
    have hs := norm_point_sq (3*v/2) (-h₀*v)
    change ‖positivePoint v‖^2=(3*v/2)^2+(-h₀*v)^2 at hs
    have hn0 := norm_nonneg (positivePoint v)
    ring_nf at hs
    rw [ExtremeTriangle.halfRoot_sq] at hs
    nlinarith [mul_pos hv0 (show 0<4/25-v by linarith [hab.2]),
      sq_nonneg (‖positivePoint v‖-1/2)]

theorem three_left_endpoint {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    point (-(1+a h.cover 3)/2) (h₀*(a h.cover 3-1))∈(rotateConfig config 3).region := by
  have hp := left_endpoint h.cover 3
    ⟨(leftReach h.cover 3).positive.le,(leftReach h.cover 3).lt_one.le⟩ le_rfl
  change AffineMap.lineMap (vertex 3) (vertex ((3:Fin 6)-1)) (a h.cover 3)∈
    (rotateConfig config 3).region at hp
  have he : AffineMap.lineMap (vertex 3) (vertex ((3:Fin 6)-1)) (a h.cover 3)=
      point (-(1+a h.cover 3)/2) (h₀*(a h.cover 3-1)) := by
    ext i
    fin_cases i <;> simp [vertex_table,AffineMap.lineMap_apply] <;> ring
  rwa [he] at hp

theorem actual_midpoint_others {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    {v : ℝ} (hv : 0<v) (i : Fin 6) (hi : i≠4) :
    midpoint v∉(rotateConfig config i.castSucc).region := by
  have hh := ExtremeTriangle.halfRoot_pos
  fin_cases i
  · apply E4Outside.exclude_far _ (GapForcedPoint.zero_endpoint h)
    have hb := SoleGapArea.b0_four_fifths h sole
    have hsq := mul_nonneg (show 0≤b h.cover 0-4/5 by linarith)
      (show 0≤b h.cover 0+4/5 by linarith)
    norm_num [midpoint,dist_point_sq]
    ring_nf
    rw [ExtremeTriangle.halfRoot_sq]
    nlinarith [sq_nonneg v]
  · apply E4Outside.exclude_far _ (anchors h.cover 1)
    norm_num [midpoint,vertex_table,dist_point_sq]
    nlinarith [sq_pos_of_pos (mul_pos hh (show 0<v+1 by linarith))]
  · apply E4Outside.exclude_far _ (anchors h.cover 2)
    norm_num [midpoint,vertex_table,dist_point_sq]
    nlinarith [sq_nonneg (h₀*v)]
  · apply E4Outside.exclude_far _ (three_left_endpoint h)
    have ha : 0<a h.cover 3 := (leftReach h.cover 3).positive
    rw [midpoint,dist_point_sq]
    nlinarith [sq_nonneg (a h.cover 3),sq_nonneg (-h₀*v-h₀*(a h.cover 3-1))]
  · exact (hi rfl).elim
  · intro hp
    have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩
    have hd := HeavyDepthTransport.actual_source_depth h (by linarith) (midpoint v) hp
    have hw := HeavyDepth.W_lt_thirtytwo hM
    dsimp [HeavyDepth.upperDepth,midpoint] at hd
    norm_num at hd
    nlinarith [mul_pos hh hv]

#print axioms actual_positive_others
#print axioms actual_midpoint_others
end
end HexagonCover.E4T4Points
