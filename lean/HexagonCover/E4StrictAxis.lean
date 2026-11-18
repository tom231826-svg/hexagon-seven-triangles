import HexagonCover.ContinuousSupportWeak
import HexagonCover.SourceCoordinates

/-! Source-exposed strict-anchor lemma for the sole E4 gap. A closed unit
equality packet exists, so its strict origin is essential. All six pair/sign
events are checked over the full real interval; normal roles use the previously
proved symmetry theorem. -/
namespace HexagonCover.E4StrictAxis
noncomputable section
open TriangleFrame SupportGeometry ContinuousSupport
local notation "h" => NICertificate.halfRoot

def points (z : ℝ) : Fin 3 → Plane :=
  ![point 0 0, point (1/2) 0, point (1/2-z) h]

def selected (j k : Fin 3) (negative : Bool) : Fin 3 → Fin 3 :=
  match j.val,k.val,negative with
  | 0,1,false => ![2,0,1]
  | 0,1,true => ![0,2,2]
  | 0,2,false => ![0,1,2]
  | 0,2,true => ![1,2,0]
  | 1,2,false => ![0,1,2]
  | 1,2,true => ![1,2,0]
  | _,_,_ => ![0,0,0]

theorem events {z : ℝ} (hz : 0 < z) (hz' : z < (1:ℝ)/4)
    (j k : Fin 3) (hjk : j < k) (negative : Bool) :
    0 ≤ selectedSum (points z) j k 0 negative (selected j k negative) ∧
    h^2*‖points z k-points z j‖^2 ≤
      (selectedSum (points z) j k 0 negative (selected j k negative))^2 ∧
    (h^2*‖points z k-points z j‖^2 <
      (selectedSum (points z) j k 0 negative (selected j k negative))^2 ∨
      ∃i,points z (selected j k negative i)=0) := by
  have hd : ‖points z k-points z j‖^2 =
      ((points z k) 0-(points z j) 0)^2+((points z k) 1-(points z j) 1)^2 := by
    simpa only [dist_eq_norm] using dist_sq_coordinates (points z k) (points z j)
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
  have hz2 : z^2 < z/4 := by nlinarith [mul_pos hz (sub_pos.mpr hz')]
  have hz3 : z^3 ≤ z^2/4 := by nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz'.le)]
  fin_cases j <;> fin_cases k <;> cases negative <;> norm_num at hjk
  all_goals refine ⟨?_,?_,Or.inr ?_⟩
  all_goals first
    | exact ⟨0,point_zero⟩
    | exact ⟨1,point_zero⟩
    | exact ⟨2,point_zero⟩
    | (norm_num [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
        perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point] <;>
       ring_nf <;>
       (try simp only [hh,hh3,hh4,hh6]) <;>
       nlinarith [sq_nonneg (z^2),mul_pos hh0 hz,mul_pos hh0 (sub_pos.mpr hz'),
         mul_nonneg hh0.le (sq_nonneg z)])

theorem injective {z : ℝ} (hz : 0 < z) (hz' : z < (1:ℝ)/4) :
    Function.Injective (points z) := by
  intro i j he
  have hx := congrArg (fun p:Plane => p 0) he
  have hy := congrArg (fun p:Plane => p 1) he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
        Matrix.head_cons,Fin.reduceFinMk,point_coord_zero,point_coord_one] at hx hy
       exfalso
       linarith [ExtremeTriangle.halfRoot_pos])

theorem impossible {z r : ℝ} (hz : 0 < z) (hz' : z < (1:ℝ)/4)
    (T : UnitTriangle) (hr : 0 < r) (hball : Metric.ball (0:Plane) r ⊆ T.region)
    (contained : ∀i,points z i∈T.region) : False :=
  ContinuousSupportWeak.impossible (points z) (injective hz hz')
    (j:=0) (k:=1) (by decide) selected (events hz hz') T hr hball contained

/-- Translation of one and the same actual triangle. -/
def shiftTriangle (T : UnitTriangle) (u : Plane) : UnitTriangle :=
  Symmetry.mapTriangle (AffineIsometryEquiv.vaddConst ℝ u).symm T

theorem mem_shift (T : UnitTriangle) (u p : Plane) :
    p-u∈(shiftTriangle T u).region ↔ p∈T.region := by
  rw [shiftTriangle,Symmetry.map_region]
  constructor
  · rintro ⟨q,hq,he⟩
    have he' : q-u=p-u := he
    exact (sub_left_injective he') ▸ hq
  · exact fun hp => ⟨p,hp,rfl⟩

theorem ball_shift (T : UnitTriangle) (u : Plane) {r : ℝ}
    (hb : Metric.ball u r ⊆ T.region) :
    Metric.ball (0:Plane) r ⊆ (shiftTriangle T u).region := by
  intro p hp
  have hm : p+u∈T.region := hb (by simpa only [Metric.mem_ball,dist_eq_norm,
    add_sub_cancel_right,sub_zero] using hp)
  have hs := (mem_shift T u (p+u)).mpr hm
  simpa only [add_sub_cancel_right] using hs

theorem translated_exclusion {z r : ℝ} (hz : 0 < z) (hz' : z < (1:ℝ)/4)
    (T : UnitTriangle) (u : Plane) (hr : 0 < r)
    (hball : Metric.ball u r ⊆ T.region)
    (hB : u+point (1/2) 0∈T.region) : u+point (1/2-z) h∉T.region := by
  intro hV
  apply impossible hz hz' (shiftTriangle T u) hr (ball_shift T u hball)
  intro i
  have hm : u+points z i∈T.region := by
    fin_cases i
    · simpa [points] using hball (Metric.mem_ball_self hr)
    · exact hB
    · exact hV
  have hs := (mem_shift T u (u+points z i)).mpr hm
  simpa only [add_sub_cancel_left] using hs

#print axioms translated_exclusion
end
end HexagonCover.E4StrictAxis
