import HexagonCover.ContinuousSupport

/-! Source-exposed Pa packet, using the corrected positive y-coordinate in
its rotated D--O normal. Midpoint choices merely select lower support branches;
every identity and full real-interval inequality below is checked by Lean. -/
namespace HexagonCover.PaSupportArithmetic
noncomputable section
open TriangleFrame SupportGeometry ContinuousSupport
local notation "h" => NICertificate.halfRoot

def points (a : ℝ) : Fin 4 → Plane :=
  ![point 0 0,point (3/5) (7*h/15),point (1-a/2) (-h*a),point 0 (-h*a)]

def selected (j k : Fin 4) (negative : Bool) : Fin 3 → Fin 4 :=
  match j.val,k.val,negative with
  | 0,1,false => ![0,3,2]
  | 0,1,true => ![2,1,3]
  | 0,2,false => ![1,3,2]
  | 0,2,true => ![3,2,0]
  | 0,3,false => ![2,1,3]
  | 0,3,true => ![0,2,1]
  | 1,2,false => ![1,0,2]
  | 1,2,true => ![3,2,1]
  | 1,3,false => ![2,1,3]
  | 1,3,true => ![0,3,2]
  | 2,3,false => ![2,2,0]
  | 2,3,true => ![1,3,2]
  | _,_,_ => ![0,0,0]

private theorem point_sub_sq (x y u v : ℝ) :
    ‖point x y-point u v‖^2=(x-u)^2+(y-v)^2 := by
  rw [←dist_eq_norm,dist_point_sq]

private theorem event_01_0 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 0 1 0 false (selected 0 1 false) ∧
    h^2*‖points a 1-points a 0‖^2 ≤ (selectedSum (points a) 0 1 0 false (selected 0 1 false))^2 ∧
    (h^2*‖points a 1-points a 0‖^2 < (selectedSum (points a) 0 1 0 false (selected 0 1 false))^2 ∨
      ∃i,points a (selected 0 1 false i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 0 1 0 false (selected 0 1 false)=h*((5/6 : ℝ) + (11/60 : ℝ)*a^1) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 1-points a 0‖^2=((157/300 : ℝ)) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((5/6 : ℝ) + (11/60 : ℝ)*a^1) := by
    calc
      ((5/6 : ℝ) + (11/60 : ℝ)*a^1) = (5/6 : ℝ)*(25*a/4)^0*(1-25*a/4)^1 + (647/750 : ℝ)*(25*a/4)^1*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((5/6 : ℝ) + (11/60 : ℝ)*a^1)^2-((157/300 : ℝ)) := by
    calc
      ((5/6 : ℝ) + (11/60 : ℝ)*a^1)^2-((157/300 : ℝ)) = (77/450 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (88/225 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (62117/281250 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((157/300 : ℝ)) < (h*((5/6 : ℝ) + (11/60 : ℝ)*a^1))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_01_1 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 0 1 0 true (selected 0 1 true) ∧
    h^2*‖points a 1-points a 0‖^2 ≤ (selectedSum (points a) 0 1 0 true (selected 0 1 true))^2 ∧
    (h^2*‖points a 1-points a 0‖^2 < (selectedSum (points a) 0 1 0 true (selected 0 1 true))^2 ∨
      ∃i,points a (selected 0 1 true i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 0 1 0 true (selected 0 1 true)=h*((99/100 : ℝ) + (5/12 : ℝ)*a^1) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 1-points a 0‖^2=((157/300 : ℝ)) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((99/100 : ℝ) + (5/12 : ℝ)*a^1) := by
    calc
      ((99/100 : ℝ) + (5/12 : ℝ)*a^1) = (99/100 : ℝ)*(25*a/4)^0*(1-25*a/4)^1 + (317/300 : ℝ)*(25*a/4)^1*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((99/100 : ℝ) + (5/12 : ℝ)*a^1)^2-((157/300 : ℝ)) := by
    calc
      ((99/100 : ℝ) + (5/12 : ℝ)*a^1)^2-((157/300 : ℝ)) = (13703/30000 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (15683/15000 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (53389/90000 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((157/300 : ℝ)) < (h*((99/100 : ℝ) + (5/12 : ℝ)*a^1))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_02_0 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 0 2 0 false (selected 0 2 false) ∧
    h^2*‖points a 2-points a 0‖^2 ≤ (selectedSum (points a) 0 2 0 false (selected 0 2 false))^2 ∧
    (h^2*‖points a 2-points a 0‖^2 < (selectedSum (points a) 0 2 0 false (selected 0 2 false))^2 ∨
      ∃i,points a (selected 0 2 false i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 0 2 0 false (selected 0 2 false)=h*((22/15 : ℝ) + (-2/15 : ℝ)*a^1) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 2-points a 0‖^2=((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((22/15 : ℝ) + (-2/15 : ℝ)*a^1) := by
    calc
      ((22/15 : ℝ) + (-2/15 : ℝ)*a^1) = (22/15 : ℝ)*(25*a/4)^0*(1-25*a/4)^1 + (542/375 : ℝ)*(25*a/4)^1*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((22/15 : ℝ) + (-2/15 : ℝ)*a^1)^2-((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    calc
      ((22/15 : ℝ) + (-2/15 : ℝ)*a^1)^2-((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) = (259/225 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (13498/5625 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (172039/140625 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) < (h*((22/15 : ℝ) + (-2/15 : ℝ)*a^1))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_02_1 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 0 2 0 true (selected 0 2 true) ∧
    h^2*‖points a 2-points a 0‖^2 ≤ (selectedSum (points a) 0 2 0 true (selected 0 2 true))^2 ∧
    (h^2*‖points a 2-points a 0‖^2 < (selectedSum (points a) 0 2 0 true (selected 0 2 true))^2 ∨
      ∃i,points a (selected 0 2 true i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 0 2 0 true (selected 0 2 true)=h*((1 : ℝ) + (1/2 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 2-points a 0‖^2=((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((1 : ℝ) + (1/2 : ℝ)*a^2) := by
    calc
      ((1 : ℝ) + (1/2 : ℝ)*a^2) = (1 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (2 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (633/625 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((1 : ℝ) + (1/2 : ℝ)*a^2)^2-((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    calc
      ((1 : ℝ) + (1/2 : ℝ)*a^2)^2-((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) = (4/25 : ℝ)*(25*a/4)^1*(1-25*a/4)^3 + (12/25 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (12/25 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (62564/390625 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((1 : ℝ) + (-1 : ℝ)*a^1 + (1 : ℝ)*a^2) < (h*((1 : ℝ) + (1/2 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_03_0 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 0 3 0 false (selected 0 3 false) ∧
    h^2*‖points a 3-points a 0‖^2 ≤ (selectedSum (points a) 0 3 0 false (selected 0 3 false))^2 ∧
    (h^2*‖points a 3-points a 0‖^2 < (selectedSum (points a) 0 3 0 false (selected 0 3 false))^2 ∨
      ∃i,points a (selected 0 3 false i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 0 3 0 false (selected 0 3 false)=h*((21/20 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 3-points a 0‖^2=((3/4 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((21/20 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    calc
      ((21/20 : ℝ)*a^1 + (1/4 : ℝ)*a^2) = (21/125 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (109/625 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((21/20 : ℝ)*a^1 + (1/4 : ℝ)*a^2)^2-((3/4 : ℝ)*a^2) := by
    calc
      ((21/20 : ℝ)*a^1 + (1/4 : ℝ)*a^2)^2-((3/4 : ℝ)*a^2) = (141/15625 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (1578/78125 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (4381/390625 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((3/4 : ℝ)*a^2) < (h*((21/20 : ℝ)*a^1 + (1/4 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_03_1 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 0 3 0 true (selected 0 3 true) ∧
    h^2*‖points a 3-points a 0‖^2 ≤ (selectedSum (points a) 0 3 0 true (selected 0 3 true))^2 ∧
    (h^2*‖points a 3-points a 0‖^2 < (selectedSum (points a) 0 3 0 true (selected 0 3 true))^2 ∨
      ∃i,points a (selected 0 3 true i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 0 3 0 true (selected 0 3 true)=h*((23/20 : ℝ)*a^1 + (1/2 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 3-points a 0‖^2=((3/4 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((23/20 : ℝ)*a^1 + (1/2 : ℝ)*a^2) := by
    calc
      ((23/20 : ℝ)*a^1 + (1/2 : ℝ)*a^2) = (23/125 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (123/625 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((23/20 : ℝ)*a^1 + (1/2 : ℝ)*a^2)^2-((3/4 : ℝ)*a^2) := by
    calc
      ((23/20 : ℝ)*a^1 + (1/2 : ℝ)*a^2)^2-((3/4 : ℝ)*a^2) = (229/15625 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (2658/78125 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (7629/390625 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((3/4 : ℝ)*a^2) < (h*((23/20 : ℝ)*a^1 + (1/2 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_12_0 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 1 2 0 false (selected 1 2 false) ∧
    h^2*‖points a 2-points a 1‖^2 ≤ (selectedSum (points a) 1 2 0 false (selected 1 2 false))^2 ∧
    (h^2*‖points a 2-points a 1‖^2 < (selectedSum (points a) 1 2 0 false (selected 1 2 false))^2 ∨
      ∃i,points a (selected 1 2 false i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 1 2 0 false (selected 1 2 false)=h*((19/30 : ℝ) + (-1/6 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 2-points a 1‖^2=((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((19/30 : ℝ) + (-1/6 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    calc
      ((19/30 : ℝ) + (-1/6 : ℝ)*a^1 + (1 : ℝ)*a^2) = (19/30 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (31/25 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (2371/3750 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((19/30 : ℝ) + (-1/6 : ℝ)*a^1 + (1 : ℝ)*a^2)^2-((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    calc
      ((19/30 : ℝ) + (-1/6 : ℝ)*a^1 + (1 : ℝ)*a^2)^2-((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) = (7/90 : ℝ)*(25*a/4)^0*(1-25*a/4)^4 + (86/375 : ℝ)*(25*a/4)^1*(1-25*a/4)^3 + (6437/28125 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (1242/15625 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (19883/7031250 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) < (h*((19/30 : ℝ) + (-1/6 : ℝ)*a^1 + (1 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_12_1 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 1 2 0 true (selected 1 2 true) ∧
    h^2*‖points a 2-points a 1‖^2 ≤ (selectedSum (points a) 1 2 0 true (selected 1 2 true))^2 ∧
    (h^2*‖points a 2-points a 1‖^2 < (selectedSum (points a) 1 2 0 true (selected 1 2 true))^2 ∨
      ∃i,points a (selected 1 2 true i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 1 2 0 true (selected 1 2 true)=h*((79/100 : ℝ) + (16/15 : ℝ)*a^1 + (1/2 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 2-points a 1‖^2=((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((79/100 : ℝ) + (16/15 : ℝ)*a^1 + (1/2 : ℝ)*a^2) := by
    calc
      ((79/100 : ℝ) + (16/15 : ℝ)*a^1 + (1/2 : ℝ)*a^2) = (79/100 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (1313/750 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (7301/7500 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((79/100 : ℝ) + (16/15 : ℝ)*a^1 + (1/2 : ℝ)*a^2)^2-((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) := by
    calc
      ((79/100 : ℝ) + (16/15 : ℝ)*a^1 + (1/2 : ℝ)*a^2)^2-((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) = (9023/30000 : ℝ)*(25*a/4)^0*(1-25*a/4)^4 + (17809/12500 : ℝ)*(25*a/4)^1*(1-25*a/4)^3 + (112199/45000 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (5399713/2812500 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (30977101/56250000 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((97/300 : ℝ) + (3/10 : ℝ)*a^1 + (1 : ℝ)*a^2) < (h*((79/100 : ℝ) + (16/15 : ℝ)*a^1 + (1/2 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_13_0 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 1 3 0 false (selected 1 3 false) ∧
    h^2*‖points a 3-points a 1‖^2 ≤ (selectedSum (points a) 1 3 0 false (selected 1 3 false))^2 ∧
    (h^2*‖points a 3-points a 1‖^2 < (selectedSum (points a) 1 3 0 false (selected 1 3 false))^2 ∨
      ∃i,points a (selected 1 3 false i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 1 3 0 false (selected 1 3 false)=h*((99/100 : ℝ) + (22/15 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 3-points a 1‖^2=((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((99/100 : ℝ) + (22/15 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    calc
      ((99/100 : ℝ) + (22/15 : ℝ)*a^1 + (1/4 : ℝ)*a^2) = (99/100 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (1661/750 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (9233/7500 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((99/100 : ℝ) + (22/15 : ℝ)*a^1 + (1/4 : ℝ)*a^2)^2-((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) := by
    calc
      ((99/100 : ℝ) + (22/15 : ℝ)*a^1 + (1/4 : ℝ)*a^2)^2-((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) = (13703/30000 : ℝ)*(25*a/4)^0*(1-25*a/4)^4 + (81739/37500 : ℝ)*(25*a/4)^1*(1-25*a/4)^3 + (4327943/1125000 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (8395513/2812500 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (48430789/56250000 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) < (h*((99/100 : ℝ) + (22/15 : ℝ)*a^1 + (1/4 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_13_1 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 1 3 0 true (selected 1 3 true) ∧
    h^2*‖points a 3-points a 1‖^2 ≤ (selectedSum (points a) 1 3 0 true (selected 1 3 true))^2 ∧
    (h^2*‖points a 3-points a 1‖^2 < (selectedSum (points a) 1 3 0 true (selected 1 3 true))^2 ∨
      ∃i,points a (selected 1 3 true i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 1 3 0 true (selected 1 3 true)=h*((5/6 : ℝ) + (41/60 : ℝ)*a^1 + (-1/4 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 3-points a 1‖^2=((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((5/6 : ℝ) + (41/60 : ℝ)*a^1 + (-1/4 : ℝ)*a^2) := by
    calc
      ((5/6 : ℝ) + (41/60 : ℝ)*a^1 + (-1/4 : ℝ)*a^2) = (5/6 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (222/125 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (3511/3750 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((5/6 : ℝ) + (41/60 : ℝ)*a^1 + (-1/4 : ℝ)*a^2)^2-((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) := by
    calc
      ((5/6 : ℝ) + (41/60 : ℝ)*a^1 + (-1/4 : ℝ)*a^2)^2-((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) = (77/450 : ℝ)*(25*a/4)^0*(1-25*a/4)^4 + (283/375 : ℝ)*(25*a/4)^1*(1-25*a/4)^3 + (171481/140625 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (201067/234375 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (1561373/7031250 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((157/300 : ℝ) + (7/10 : ℝ)*a^1 + (3/4 : ℝ)*a^2) < (h*((5/6 : ℝ) + (41/60 : ℝ)*a^1 + (-1/4 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

private theorem event_23_0 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 2 3 0 false (selected 2 3 false) ∧
    h^2*‖points a 3-points a 2‖^2 ≤ (selectedSum (points a) 2 3 0 false (selected 2 3 false))^2 ∧
    (h^2*‖points a 3-points a 2‖^2 < (selectedSum (points a) 2 3 0 false (selected 2 3 false))^2 ∨
      ∃i,points a (selected 2 3 false i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 2 3 0 false (selected 2 3 false)=h*((1 : ℝ) + (-1/2 : ℝ)*a^1) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 3-points a 2‖^2=((1 : ℝ) + (-1 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((1 : ℝ) + (-1/2 : ℝ)*a^1) := by
    calc
      ((1 : ℝ) + (-1/2 : ℝ)*a^1) = (1 : ℝ)*(25*a/4)^0*(1-25*a/4)^1 + (23/25 : ℝ)*(25*a/4)^1*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  rw [hs,hd]
  refine ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,?_,Or.inr ?_⟩
  · apply le_of_eq
    ring
  · exact ⟨2,by simp [points,selected]⟩

private theorem event_23_1 {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ selectedSum (points a) 2 3 0 true (selected 2 3 true) ∧
    h^2*‖points a 3-points a 2‖^2 ≤ (selectedSum (points a) 2 3 0 true (selected 2 3 true))^2 ∧
    (h^2*‖points a 3-points a 2‖^2 < (selectedSum (points a) 2 3 0 true (selected 2 3 true))^2 ∨
      ∃i,points a (selected 2 3 true i)=0) := by
  have ht0 : 0 < 25*a/4 := by positivity
  have ht1 : 0 < 1-25*a/4 := by linarith
  have h3 : h^3=(3/4)*h := by nlinarith [congrArg (fun x:ℝ => h*x) ExtremeTriangle.halfRoot_sq]
  have hs : selectedSum (points a) 2 3 0 true (selected 2 3 true)=h*((22/15 : ℝ) + (-7/30 : ℝ)*a^1 + (-1/4 : ℝ)*a^2) := by
    simp [selectedSum,branch,Fin.sum_univ_three,eventBase,signedPerpendicular,
      perpendicular,inverseRole,nvec,NICertificate.normalValues,dotp,points,selected,point]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq,h3] <;> ring
  have hd : ‖points a 3-points a 2‖^2=((1 : ℝ) + (-1 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    simp only [points,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Fin.reduceFinMk,point_sub_sq]
    ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring
  have hf : 0 < ((22/15 : ℝ) + (-7/30 : ℝ)*a^1 + (-1/4 : ℝ)*a^2) := by
    calc
      ((22/15 : ℝ) + (-7/30 : ℝ)*a^1 + (-1/4 : ℝ)*a^2) = (22/15 : ℝ)*(25*a/4)^0*(1-25*a/4)^2 + (362/125 : ℝ)*(25*a/4)^1*(1-25*a/4)^1 + (2668/1875 : ℝ)*(25*a/4)^2*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hp : 0 < ((22/15 : ℝ) + (-7/30 : ℝ)*a^1 + (-1/4 : ℝ)*a^2)^2-((1 : ℝ) + (-1 : ℝ)*a^1 + (1/4 : ℝ)*a^2) := by
    calc
      ((22/15 : ℝ) + (-7/30 : ℝ)*a^1 + (-1/4 : ℝ)*a^2)^2-((1 : ℝ) + (-1 : ℝ)*a^1 + (1/4 : ℝ)*a^2) = (259/225 : ℝ)*(25*a/4)^0*(1-25*a/4)^4 + (8728/1875 : ℝ)*(25*a/4)^1*(1-25*a/4)^3 + (989206/140625 : ℝ)*(25*a/4)^2*(1-25*a/4)^2 + (1103632/234375 : ℝ)*(25*a/4)^3*(1-25*a/4)^1 + (4142599/3515625 : ℝ)*(25*a/4)^4*(1-25*a/4)^0 := by ring
      _ > 0 := by positivity
  have hstrict : h^2*((1 : ℝ) + (-1 : ℝ)*a^1 + (1/4 : ℝ)*a^2) < (h*((22/15 : ℝ) + (-7/30 : ℝ)*a^1 + (-1/4 : ℝ)*a^2))^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ExtremeTriangle.halfRoot_pos) hp]
  rw [hs,hd]
  exact ⟨(mul_pos ExtremeTriangle.halfRoot_pos hf).le,hstrict.le,Or.inl hstrict⟩

set_option maxHeartbeats 800000 in
theorem checked {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    ∀j k:Fin 4,j < k → ∀negative,
      0 ≤ selectedSum (points a) j k 0 negative (selected j k negative) ∧
      h^2*‖points a k-points a j‖^2 ≤
        (selectedSum (points a) j k 0 negative (selected j k negative))^2 ∧
      (h^2*‖points a k-points a j‖^2 <
        (selectedSum (points a) j k 0 negative (selected j k negative))^2 ∨
        ∃i,points a (selected j k negative i)=0) := by
  intro j k hjk negative
  fin_cases j <;> fin_cases k <;> try (norm_num at hjk)
  · cases negative
    · exact event_01_0 ha ha1
    · exact event_01_1 ha ha1
  · cases negative
    · exact event_02_0 ha ha1
    · exact event_02_1 ha ha1
  · cases negative
    · exact event_03_0 ha ha1
    · exact event_03_1 ha ha1
  · cases negative
    · exact event_12_0 ha ha1
    · exact event_12_1 ha ha1
  · cases negative
    · exact event_13_0 ha ha1
    · exact event_13_1 ha ha1
  · cases negative
    · exact event_23_0 ha ha1
    · exact event_23_1 ha ha1

end
end HexagonCover.PaSupportArithmetic
