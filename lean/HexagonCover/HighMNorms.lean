import HexagonCover.HighMPoints
import HexagonCover.HighMScalar

/-! Exact Euclidean norm identities for the same high-M support-line points. -/
namespace HexagonCover.HighMNorms
noncomputable section
open TriangleFrame HeavyDepth HighMChart HighMPoints HighMScalar
local notation "h₀" => NICertificate.halfRoot

def ahat (D r : ℝ) : ℝ := 1+r-D*S r/h₀
def Xhat (D r : ℝ) : Plane := point (ahat D r-1/2) h₀
def V4 (M : ℝ) : Plane := point (M-1/2) (-h₀)

theorem dist_residual_sq (r D k : ℝ) (V : Plane) :
    dist (residual r D k) V^2 = D^2*(1+k^2) -
      2*D*(dotp (inward r) V+k*dotp (tangent r) V)+dotp V V := by
  rw [dist_sq_coordinates,residual_x,residual_y]
  have hu := inward_unit r
  have hm := congrArg (fun z : ℝ => D^2*(1+k^2)*z) hu
  dsimp [dotp,tangent] at hm ⊢
  nlinarith only [hm]

theorem sign_difference (r D q : ℝ) (V : Plane) :
    dist (residual r D q) V^2-dist (residual r D (-q)) V^2 =
      -4*q*D*dotp (tangent r) V := by
  rw [dist_residual_sq,dist_residual_sq]
  ring

theorem inv_height : h₀⁻¹=4*h₀/3 := by
  rw [inv_eq_one_div]
  apply (div_eq_iff (ne_of_gt ExtremeTriangle.halfRoot_pos)).mpr
  nlinarith only [ExtremeTriangle.halfRoot_sq]

theorem zero_minus_identity (D r : ℝ) :
    dist (residual r D (-q)) (Xhat D r)^2-1 = X D r := by
  rw [dist_residual_sq]
  unfold Xhat ahat
  simp only [div_eq_mul_inv,inv_height]
  dsimp [inward,tangent,dotp]
  unfold X C L
  field_simp [ne_of_gt (S_pos r)]
  ring_nf
  have hs3 : (S r)^3=CornerChart.Q r*S r := by rw [pow_succ,S_sq]
  have hh3 : h₀^3=(3/4:ℝ)*h₀ := by rw [pow_succ,ExtremeTriangle.halfRoot_sq]
  simp only [hs3,S_sq,hh3,ExtremeTriangle.halfRoot_sq]
  unfold CornerChart.Q
  ring

theorem fourth_plus_identity (D M r : ℝ) :
    dist (residual r D q) (V4 M)^2-1 = X4 D M r := by
  rw [dist_residual_sq]
  dsimp [inward,tangent,dotp,V4]
  unfold X4 G
  field_simp [ne_of_gt (S_pos r)]
  ring_nf
  rw [ExtremeTriangle.halfRoot_sq]
  ring

/-- Moving an actual comparison point further left cannot reduce its distance
to the residual point, whose x-coordinate lies to its right. -/
theorem left_comparison (p : Plane) {x0 x1 y : ℝ} (hx : x0≤x1) (hp : x1≤p 0) :
    dist p (point x1 y)^2≤dist p (point x0 y)^2 := by
  rw [dist_sq_coordinates,dist_sq_coordinates]
  simp only [point_coord_zero,point_coord_one]
  have hprod := mul_nonneg (sub_nonneg.mpr hx) (show 0≤2*p 0-x1-x0 by linarith)
  nlinarith only [hprod]

end
end HexagonCover.HighMNorms

#print axioms HexagonCover.HighMNorms.zero_minus_identity
#print axioms HexagonCover.HighMNorms.fourth_plus_identity
