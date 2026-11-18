import HexagonCover.ContinuousSupportSymmetry

/-! The source-exposed four-point packet for the A-outside-T2 branch.
Midpoint-selected indices are candidates only. The theorem checks the entire
open real interval, independently of that midpoint evaluation. -/
namespace HexagonCover.SoleOutsidePacket
open TriangleFrame SupportGeometry ContinuousSupport
noncomputable section
local notation "h" => NICertificate.halfRoot

def points (w : ℝ) : Fin 4 → Plane :=
  ![point 0 0,point (31/100) (-h),point (1/2-w) (-h),point w 0]
def selected (i j : Fin 4) (negative : Bool) : Fin 3 → Fin 4 :=
  match i.val,j.val,negative with
  | 0,1,false => ![2,0,1]
  | 0,1,true => ![0,2,3]
  | 0,2,false => ![3,0,1]
  | 0,2,true => ![1,2,3]
  | 0,3,false => ![0,1,2]
  | 0,3,true => ![1,3,0]
  | 1,2,false => ![0,1,2]
  | 1,2,true => ![1,3,0]
  | 1,3,false => ![0,2,3]
  | 1,3,true => ![2,0,1]
  | 2,3,false => ![1,2,3]
  | 2,3,true => ![2,0,1]
  | _,_,_ => ![0,0,0]

set_option maxHeartbeats 2000000 in
theorem events {w : ℝ} (hw : 0 < w) (hw' : w < (2:ℝ)/25)
    (i j : Fin 4) (hij : i < j) (negative : Bool) :
    0 < selectedSum (points w) i j 0 negative (selected i j negative) ∧
    h^2*‖points w j-points w i‖^2 <
      (selectedSum (points w) i j 0 negative (selected i j negative))^2 := by
  have hd : ‖points w j-points w i‖^2 =
      ((points w j) 0-(points w i) 0)^2+((points w j) 1-(points w i) 1)^2 := by
    simpa only [dist_eq_norm] using dist_sq_coordinates (points w j) (points w i)
  rw [hd]
  have hh := ExtremeTriangle.halfRoot_sq
  have hh0 := ExtremeTriangle.halfRoot_pos
  have hh3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) hh]
  have hh4 : h^4=(9:ℝ)/16 := by
    calc h^4=(h^2)^2 := by ring
         _=9/16 := by rw [hh]; norm_num
  have hh6 : h^6=(27:ℝ)/64 := by
    calc h^6=(h^2)^3 := by ring
         _=27/64 := by rw [hh]; norm_num
  have hw2 : w^2 < (2:ℝ)/25*w := by
    nlinarith only [mul_pos hw (sub_pos.mpr hw')]
  have hw3 : 0 < w^3 := pow_pos hw 3
  have hw19 : 0 < 19/100-w := by linarith only [hw']
  fin_cases i <;> fin_cases j <;> cases negative <;> norm_num at hij
  all_goals
    clear hd hij
    norm_num [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf
    simp only [hh,hh3,hh4,hh6]
    constructor
    · nlinarith [mul_pos hh0 hw,mul_pos hh0 hw19]
    · nlinarith [sq_nonneg (w^2),mul_pos hw hw19]

theorem impossible {w : ℝ} (hw : 0 < w) (hw' : w < (2:ℝ)/25)
    (T : UnitTriangle) (contained : ∀i,points w i∈T.region) : False := by
  apply ContinuousSupportSymmetry.impossible (points w) (a:=0) (b:=1) ?_
    selected (events hw hw') T contained
  intro he
  have hy := congrArg (fun p : Plane=>p 1) he
  norm_num [points,point] at hy
  linarith [ExtremeTriangle.halfRoot_pos]

end
end HexagonCover.SoleOutsidePacket
