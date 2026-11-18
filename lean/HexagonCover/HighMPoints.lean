import HexagonCover.HighMChart

/-! Shared actual-point geometry for the three source high-M intervals. -/
namespace HexagonCover.HighMPoints
noncomputable section
open TriangleFrame HeavyDepth HighMChart SourceCoordinates HexagonCover.Configuration NormalizedHeavy
local notation "h₀" => NICertificate.halfRoot

def tangent (r : ℝ) : Plane := point ((inward r) 1) (-((inward r) 0))
def residual (r D k : ℝ) : Plane := D • inward r + (k*D) • tangent r

theorem residual_x (r D k : ℝ) :
    residual r D k 0 = D*((inward r) 0+k*(inward r) 1) := by
  simp [residual,tangent]
  ring

theorem residual_y (r D k : ℝ) :
    residual r D k 1 = D*((inward r) 1-k*(inward r) 0) := by
  simp [residual,tangent]
  ring

theorem residual_line (r D k : ℝ) : dotp (inward r) (residual r D k)=D := by
  have ht : dotp (inward r) (tangent r)=0 := by dsimp [tangent,dotp]; ring
  rw [residual,dotp_add_right,dotp_smul_right,dotp_smul_right,inward_unit,ht]
  ring

theorem residual_facet_identity (r D k : ℝ) :
    (h₀*residual r D k 0+residual r D k 1/2)*S r =
      D*(1+(1/2-k*h₀)*r) := by
  rw [residual_x,residual_y]
  dsimp [inward]
  field_simp [ne_of_gt (HeavyDepth.S_pos r)]
  ring_nf
  rw [ExtremeTriangle.halfRoot_sq]
  ring

/-- The actual upper offset is essential here: `D<h` alone does not imply
that the support-line points lie inside the right hexagon facet. -/
theorem residual_facet {T : UnitTriangle} {M a k : ℝ} (w : Witness T M a)
    (hM : 4/5<M) (hM1 : M<1) (hk0 : -1/4≤k) (hk1 : k≤1/4) :
    h₀*residual w.r w.D k 0+residual w.r w.D k 1/2<h₀ := by
  let c : ℝ := 1/2-k*h₀
  let t : ℝ := 1-M
  have hh0 := ExtremeTriangle.halfRoot_pos
  have hh1 : h₀<1 := by nlinarith [ExtremeTriangle.halfRoot_sq]
  have hkp := mul_nonneg (show 0≤k+1/4 by linarith) hh0.le
  have hkn := mul_nonneg (show 0≤1/4-k by linarith) hh0.le
  have hc0 : 0<c := by dsimp [c]; nlinarith only [hkn,hh1]
  have hc1 : c<3/4 := by dsimp [c]; nlinarith only [hkp,hh1]
  have ht0 : 0<t := by dsimp [t]; linarith
  have ht1 : t<1/5 := by dsimp [t]; linarith
  have hcoef1 : 0<1-t-c := by linarith
  have hprod := mul_lt_mul_of_pos_left hc1 ht0
  have hcoef2 : 0<1-t*c := by nlinarith only [hprod,ht1]
  have hgap := add_pos_of_pos_of_nonneg (mul_pos hcoef1 w.r_pos)
    (mul_nonneg hcoef2.le (sq_nonneg w.r))
  have hpoly : (1+w.r*t)*(1+c*w.r)<CornerChart.Q w.r := by
    unfold CornerChart.Q
    nlinarith only [hgap]
  have hfac : 0≤1+c*w.r := by linarith [mul_pos hc0 w.r_pos]
  have hDS := (le_div_iff₀ (HeavyDepth.S_pos w.r)).mp w.upper
  have hb := mul_le_mul_of_nonneg_right hDS hfac
  have hiden := residual_facet_identity w.r w.D k
  change (h₀*residual w.r w.D k 0+residual w.r w.D k 1/2)*HeavyDepth.S w.r =
    w.D*(1+c*w.r) at hiden
  have hfinal : (h₀*residual w.r w.D k 0+residual w.r w.D k 1/2)*(HeavyDepth.S w.r)^2 <
      h₀*(HeavyDepth.S w.r)^2 := by
    calc
      _ = w.D*HeavyDepth.S w.r*(1+c*w.r) := by nlinarith only [congrArg (fun z : ℝ => z*HeavyDepth.S w.r) hiden]
      _ ≤ h₀*(1+w.r*t)*(1+c*w.r) := hb
      _ < h₀*CornerChart.Q w.r := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hpoly hh0
      _ = _ := by rw [HeavyDepth.S_sq]
  exact (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos (HeavyDepth.S_pos w.r))).mp hfinal

theorem far_of_x {p q : Plane} (h : 1<p 0-q 0) : 1<dist p q^2 := by
  rw [dist_sq_coordinates]
  nlinarith [sq_nonneg (p 1-q 1)]

theorem far_of_y {p q : Plane} (h : 1<p 1-q 1) : 1<dist p q^2 := by
  rw [dist_sq_coordinates]
  nlinarith [sq_nonneg (p 0-q 0)]

theorem first_quadrant_interior {x y : ℝ} (hx : 1/2<x) (hy : 0<y)
    (hyh : y<h₀) (hfacet : h₀*x+y/2<h₀) :
    point x y∈interior (Hexagon 1) := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hhne := ne_of_gt hh
  let t := x+y/(2*h₀)
  have htpos : 0<t := by dsimp [t]; positivity
  have ht : t<1 := by
    dsimp [t]
    have hf : (h₀*x+y/2)/h₀<1 := (div_lt_one hh).mpr hfacet
    have he : (h₀*x+y/2)/h₀=x+y/(2*h₀) := by field_simp <;> ring
    rwa [he] at hf
  let z := y/(h₀*t)
  have hz0 : 0≤z := (div_pos hy (mul_pos hh htpos)).le
  have hz1 : z≤1 := by
    apply (div_le_one (mul_pos hh htpos)).mpr
    have htx : h₀*t=h₀*x+y/2 := by dsimp [t]; field_simp <;> ring
    rw [htx]
    have hm := mul_lt_mul_of_pos_left hx hh
    linarith
  let q := (1-z) • hexVertex 1 0+z • hexVertex 1 1
  have hq : q∈Hexagon 1 := (convex_hexagon 1) (hexVertex_mem 1 0)
    (hexVertex_mem 1 1) (by linarith) hz0 (by ring)
  have hp := (convex_hexagon 1).combo_interior_self_mem_interior
    (zero_mem_interior_hexagon (by norm_num : (0:ℝ)<1)) hq
    (a:=1-t) (b:=t) (by linarith) htpos.le (by ring)
  have he : (1-t) • (0:Plane)+t • q=point x y := by
    ext i
    fin_cases i
    all_goals simp [q,z,hexVertex,NICertificate.halfRoot]
    all_goals field_simp [ne_of_gt htpos,hhne,StandardCover.sqrt3_ne_zero]
    all_goals dsimp [t,NICertificate.halfRoot]
    all_goals field_simp [StandardCover.sqrt3_ne_zero]
    all_goals ring
  exact he ▸ hp

theorem zero_endpoint {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    point (1/2-b h.cover 0) h₀∈(rotateConfig config 0).region := by
  have hm := right_endpoint h.cover 0
    ⟨(rightReach h.cover 0).positive.le,(rightReach h.cover 0).lt_one.le⟩ le_rfl
  have he : AffineMap.lineMap (vertex 0) (vertex ((0:Fin 6)+1)) (b h.cover 0)=
      point (1/2-b h.cover 0) h₀ := by
    ext i
    fin_cases i <;> simp [vertex_table,AffineMap.lineMap_apply] <;> ring
  change AffineMap.lineMap (vertex 0) (vertex ((0:Fin 6)+1)) (b h.cover 0)∈
    (rotateConfig config 0).region at hm
  rwa [he] at hm

theorem fourth_left_endpoint {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    point (1/2-a h.cover 4) (-h₀)∈(rotateConfig config 4).region := by
  have hm := left_endpoint h.cover 4
    ⟨(leftReach h.cover 4).positive.le,(leftReach h.cover 4).lt_one.le⟩ le_rfl
  have he : AffineMap.lineMap (vertex 4) (vertex ((4:Fin 6)-1)) (a h.cover 4)=
      point (1/2-a h.cover 4) (-h₀) := by
    ext i
    fin_cases i <;> simp [vertex_table,AffineMap.lineMap_apply] <;> ring
  change AffineMap.lineMap (vertex 4) (vertex ((4:Fin 6)-1)) (a h.cover 4)∈
    (rotateConfig config 4).region at hm
  rwa [he] at hm

end
end HexagonCover.HighMPoints

#print axioms HexagonCover.HighMPoints.residual_line
#print axioms HexagonCover.HighMPoints.residual_facet
#print axioms HexagonCover.HighMPoints.first_quadrant_interior
#print axioms HexagonCover.HighMPoints.zero_endpoint
#print axioms HexagonCover.HighMPoints.fourth_left_endpoint
