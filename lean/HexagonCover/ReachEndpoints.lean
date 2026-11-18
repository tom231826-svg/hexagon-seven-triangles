import HexagonCover.CornerTransport

/-! The distance between the two actual exits of one outer triangle. -/
namespace HexagonCover.ReachEndpoints
open HexagonCover.Configuration
noncomputable section

theorem two_exit_distance (i : Fin 6) (a b : ℝ) :
    dist (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) a)
      (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) b)^2=a^2+a*b+b^2 := by
  have hs := TriangleFrame.dist_sq_coordinates
    (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) a)
    (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) b)
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  generalize he : dist (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) a)
    (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) b)=z at hs ⊢
  fin_cases i
  all_goals
    norm_num [hexVertex,AffineMap.lineMap_apply,point] at hs
    ring_nf at hs
    simp only [hr] at hs
    nlinarith only [hs]

theorem actual_exit_constraint {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) : (a h i)^2+a h i*b h i+(b h i)^2 ≤ 1 := by
  have hp : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) (a h i) ∈
      (config i.castSucc).region := (leftReach h i).endpoint
  have hq : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) (b h i) ∈
      (config i.castSucc).region := (rightReach h i).endpoint
  have hd := (config i.castSucc).dist_le_one hp hq
  have hs := two_exit_distance i (a h i) (b h i)
  nlinarith only [hs,hd,dist_nonneg
    (x:=AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) (a h i))
    (y:=AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) (b h i))]

theorem short_half_of_long_two_thirds {a M : ℝ} (ha : 0 ≤ a) (hM : (2:ℝ)/3 ≤ M)
    (hc : a^2+M*a+M^2 ≤ 1) : a < (1:ℝ)/2 := by
  by_contra hn
  have hhalf : (1:ℝ)/2 ≤ a := le_of_not_gt hn
  have hm0 : 0 ≤ M := by linarith
  have hprod := mul_le_mul hM hhalf (by norm_num : (0:ℝ) ≤ 1/2) hm0
  nlinarith [sq_nonneg (a-1/2),sq_nonneg (M-2/3)]

end
end HexagonCover.ReachEndpoints
