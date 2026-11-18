import HexagonCover.E4InsideActualChart
import HexagonCover.E4T4Scalar
import HexagonCover.E4InsideCentral

/-! Actual T4 third support row and strict Pa tests. The chart is obtained
from the same finite triangle's actual backward maximum, with all ties kept. -/
namespace HexagonCover.E4T4Chart
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
open E4InsideRayChart E4InsideActualChart TriangleFrame
local notation "h₀" => NICertificate.halfRoot

def normal (r : ℝ) : Plane := point (-r) ((2+r)/(2*h₀))

theorem coordinate_identity (z : Plane) :
    vertex 4+(1-z 0+z 1/(2*h₀)) • back 4+(1+z 1/h₀) • forward 4=z := by
  have hh := ne_of_gt ExtremeTriangle.halfRoot_pos
  ext i
  fin_cases i <;> norm_num [back,forward,vertex_table]
  all_goals field_simp [hh] <;> ring

theorem third_identity (r : ℝ) (z : Plane) :
    rows r (1-z 0+z 1/(2*h₀)) (1+z 1/h₀) 2=dotp (normal r) z+1+r := by
  dsimp [rows,dotp,normal]
  field_simp [ne_of_gt ExtremeTriangle.halfRoot_pos] <;> ring

theorem halfplane {T : UnitTriangle} {p : ℝ}
    (ch : Chart T (vertex 4) (back 4) (forward 4) p) :
    ∀z∈T.region,dotp (normal ch.r) z ≤ ch.e-1-ch.r := by
  intro z hz
  have hm := (ch.character (1-z 0+z 1/(2*h₀)) (1+z 1/h₀)).mp
    (by rwa [coordinate_identity]) 2
  rw [third_identity] at hm
  norm_num at hm
  linarith

theorem normal_pos {r : ℝ} (hr : -1/2<r) : 0<dotp (normal r) (normal r) := by
  have hy : 0<(2+r)/(2*h₀) := div_pos (by linarith)
    (mul_pos (by norm_num) ExtremeTriangle.halfRoot_pos)
  dsimp [dotp,normal]
  nlinarith [sq_pos_of_pos hy,sq_nonneg r]

theorem Pa_identity (a : ℝ) :
    vertex 4+(1-a/2) • back 4+(1-a) • forward 4=E4InsideCentral.Pa a := by
  ext i
  fin_cases i <;> norm_num [back,forward,vertex_table,E4InsideCentral.Pa] <;> ring

theorem Pa_tests {T : UnitTriangle} {a p : ℝ}
    (ch : Chart T (vertex 4) (back 4) (forward 4) p)
    (hp : E4InsideCentral.Pa a∈interior T.region) :
    a/2-ch.r*(1-a)<p ∧ 1-a+ch.r*(1-a/2)<ch.e := by
  have hs := ch.strict_tests (1-a/2) (1-a) (by rwa [Pa_identity])
  have h0 := hs 0
  have h2 := hs 2
  norm_num [rows] at h0 h2
  constructor <;> nlinarith only [h0,h2]

theorem actual_short_lt_four {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    a h.cover 5/2 < a h.cover 4 := by
  have hh := (structure_bounds h).1 4
  have hs := GapChains.heavy_short h
  have hb := min_le_left (a h.cover 4) (b h.cover 4)
  linarith

theorem actual_cases {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (ch : Chart (rotateConfig config 4) (vertex 4) (back 4) (forward 4) (a h.cover 4))
    (hp : E4InsideCentral.Pa (a h.cover 5)∈interior (rotateConfig config 4).region) :
    -1/2<ch.r ∧ ((ch.r<0 ∧ ch.e=b h.cover 4) ∨
      (0<ch.r ∧ ch.d=ch.r*b h.cover 4)) := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  obtain ⟨h0,h2⟩ := Pa_tests ch hp
  have hgap := (sole 4).mpr rfl
  change b h.cover 4+a h.cover 5<1 at hgap
  apply E4T4Scalar.forward_cases (b:=b h.cover 4) ha ha1 ch.first_pos
    (SoleGapArea.light_reach_order h sole 4).1 (rightReach h.cover 4).positive
    ch.d_pos h0 h2 (by linarith)
  exact forward_active h.cover 4 ch

#print axioms actual_cases
end
end HexagonCover.E4T4Chart
