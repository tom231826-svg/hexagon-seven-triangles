import HexagonCover.E4InsideCentral

/-! Same-C southwest exclusion and the mandatory actual T2-union-T3 lower
rectangle. These are continuous whole-region duties, not sampled points. -/
namespace HexagonCover.E4InsideRegion
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

theorem lower_axis_excluded (C : UnitTriangle) {a y : ℝ}
    (ha : 0 < a) (hO : (0:Plane)∈C.region) (hPa : E4InsideCentral.Pa a∉C.region)
    (hy : y ≤ -h₀*a) : point 0 y∉C.region := by
  have ha0 : 0 < h₀*a := mul_pos ExtremeTriangle.halfRoot_pos ha
  have hy0 : y < 0 := by linarith
  have hcoef : 0 ≤ (-h₀*a)/y := le_of_lt (div_pos_of_neg_of_neg (by linarith) hy0)
  have hcoef1 : (-h₀*a)/y ≤ 1 := (div_le_one_of_neg hy0).mpr hy
  intro hp
  have hm := C.convex_region hO hp (sub_nonneg.mpr hcoef1) hcoef (by ring)
  apply hPa
  have he : (1-(-h₀*a)/y) • (0:Plane)+((-h₀*a)/y) • point 0 y=
      E4InsideCentral.Pa a := by
    ext i
    fin_cases i <;> simp [E4InsideCentral.Pa]
    field_simp [ne_of_lt hy0]
  exact he ▸ hm

theorem southwest_excluded (C : UnitTriangle) {a x y : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (hO : (0:Plane)∈C.region)
    (hP : point (1-a/2) (-h₀*a)∈C.region)
    (hPa : E4InsideCentral.Pa a∉C.region) (hx : x ≤ 0) (hy : y ≤ -h₀*a) :
    point x y∉C.region := by
  let p : ℝ := 1-a/2
  have hp : 0 < p := by dsimp [p]; linarith
  have hden : 0 < p-x := by linarith
  have hsum : (-x)/(p-x)+p/(p-x)=1 := by field_simp [ne_of_gt hden]; ring
  have hc1 : 0 ≤ (-x)/(p-x) := div_nonneg (by linarith) hden.le
  have hc2 : 0 ≤ p/(p-x) := div_nonneg hp.le hden.le
  intro hq
  let z : ℝ := ((-x)/(p-x))*(-h₀*a)+(p/(p-x))*y
  have hz : z ≤ -h₀*a := by
    have ht := mul_le_mul_of_nonneg_left hy hc2
    dsimp only [z]
    nlinarith [congrArg (fun u:ℝ=>u*(-h₀*a)) hsum]
  have hm := C.convex_region hP hq hc1 hc2 hsum
  have he : ((-x)/(p-x)) • point (1-a/2) (-h₀*a)+
      (p/(p-x)) • point x y=point 0 z := by
    ext i
    fin_cases i
    · simp [p]
      field_simp [ne_of_gt hden]
      ring
    · simp [z]
  exact lower_axis_excluded C ha hO hPa hz (he ▸ hm)

theorem actual_southwest_excluded {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ -h₀*a h.cover 5) :
    point x y∉(rotateConfig config 6).region := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  apply southwest_excluded _ ha (by linarith)
    (interior_subset (CentralAxis.source_origin_interior h)) ?_
    (E4InsideCentral.actual_excluded h sole) hx hy
  have hp := CentralAxis.source_P_mem h ((sole 4).mpr rfl)
  have he : CentralAxis.P (a h.cover 5)=point (1-a h.cover 5/2) (-h₀*a h.cover 5) := by
    ext i
    fin_cases i <;> simp [CentralAxis.P,ExteriorLoss.lowerEndpoint,
      ExteriorLoss.corner,ExteriorLoss.lowerRay] <;> ring
  rwa [he] at hp

theorem center_box_mem_hexagon {x Y : ℝ} (hx : x∈Set.Icc (-1/2:ℝ) (1/2))
    (hY : Y∈Set.Icc (-1:ℝ) 1) : point x (h₀*Y)∈Hexagon 1 := by
  have hbottom := (convex_hexagon 1) (hexVertex_mem 1 4) (hexVertex_mem 1 5)
    (a:=1/2-x) (b:=x+1/2) (by linarith [hx.2]) (by linarith [hx.1]) (by ring)
  have htop := (convex_hexagon 1) (hexVertex_mem 1 2) (hexVertex_mem 1 1)
    (a:=1/2-x) (b:=x+1/2) (by linarith [hx.2]) (by linarith [hx.1]) (by ring)
  have hm := (convex_hexagon 1) hbottom htop
    (a:=(1-Y)/2) (b:=(1+Y)/2) (by linarith [hY.2]) (by linarith [hY.1]) (by ring)
  have he : ((1-Y)/2) • ((1/2-x) • hexVertex 1 4+(x+1/2) • hexVertex 1 5)+
      ((1+Y)/2) • ((1/2-x) • hexVertex 1 2+(x+1/2) • hexVertex 1 1)=point x (h₀*Y) := by
    ext i
    fin_cases i <;> simp [hexVertex,NICertificate.halfRoot] <;> ring
  exact he ▸ hm

theorem four_endpoint {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    point ((1+b h.cover 4)/2) (h₀*(b h.cover 4-1))∈(rotateConfig config 4).region := by
  have hp := right_endpoint h.cover 4
    ⟨(rightReach h.cover 4).positive.le,(rightReach h.cover 4).lt_one.le⟩ le_rfl
  change AffineMap.lineMap (vertex 4) (vertex ((4:Fin 6)+1)) (b h.cover 4)∈
    (rotateConfig config 4).region at hp
  have he : AffineMap.lineMap (vertex 4) (vertex ((4:Fin 6)+1)) (b h.cover 4)=
      point ((1+b h.cover 4)/2) (h₀*(b h.cover 4-1)) := by
    ext i
    fin_cases i <;> simp [vertex_table,AffineMap.lineMap_apply] <;> ring
  rwa [he] at hp

theorem rectangle_anchor_far {x Y : ℝ} (hx : x∈Set.Icc (-1/2:ℝ) (-1/4))
    (hY : Y∈Set.Icc (-1:ℝ) (-1/4)) (i : Fin 6)
    (hi2 : i≠2) (hi3 : i≠3) (hi4 : i≠4) :
    1 < (dist (point x (h₀*Y)) (vertex i))^2 := by
  have hprod := mul_nonneg (show 0 ≤ -Y-1/4 by linarith [hY.2])
    (show 0 ≤ -Y+9/4 by linarith [hY.2])
  fin_cases i
  all_goals try exact (hi2 rfl).elim
  all_goals try exact (hi3 rfl).elim
  all_goals try exact (hi4 rfl).elim
  all_goals norm_num [vertex_table,dist_point_sq]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals nlinarith [hx.2,hY.2,sq_nonneg x,sq_nonneg Y,sq_nonneg (x+1/2),
    sq_nonneg (x-1/2),sq_nonneg (h₀*Y),sq_nonneg (x+1/4)]

theorem rectangle_four_far {x Y b : ℝ} (hx : x ≤ -1/4) (hb : 1/2 < b) :
    1 < (dist (point x (h₀*Y)) (point ((1+b)/2) (h₀*(b-1))))^2 := by
  rw [dist_point_sq]
  have hd : 1 < (1+b)/2-x := by linarith
  nlinarith [sq_nonneg (h₀*Y-h₀*(b-1)),sq_nonneg ((1+b)/2-x-1)]

/-- Every point of the closed lower rectangle belongs to the same actual
T2 or T3. No claim assigns its whole union duty to one of the two owners. -/
theorem actual_lower_rectangle {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    {x Y : ℝ} (hx : x∈Set.Icc (-1/2:ℝ) (-1/4))
    (hY : Y∈Set.Icc (-1:ℝ) (-1/4)) :
    point x (h₀*Y)∈(rotateConfig config 2).region ∨
      point x (h₀*Y)∈(rotateConfig config 3).region := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  have hex := center_box_mem_hexagon ⟨hx.1,by linarith [hx.2]⟩ ⟨hY.1,by linarith [hY.2]⟩
  have central := actual_southwest_excluded h sole (x:=x) (y:=h₀*Y) (by linarith [hx.2])
    (show h₀*Y ≤ -h₀*a h.cover 5 by
      nlinarith [mul_nonneg ExtremeTriangle.halfRoot_pos.le
        (show 0 ≤ -a h.cover 5-Y by linarith [hY.2])])
  have outer (i : Fin 6) (hi2 : i≠2) (hi3 : i≠3) :
      point x (h₀*Y)∉(rotateConfig config i.castSucc).region := by
    intro hp
    by_cases hi4 : i=4
    · subst i
      have hd := (rotateConfig config 4).dist_le_one hp (four_endpoint h)
      have hf := rectangle_four_far (Y:=Y) hx.2 (SoleGapArea.b4_half h sole)
      nlinarith [dist_nonneg (x:=point x (h₀*Y))
        (y:=point ((1+b h.cover 4)/2) (h₀*(b h.cover 4-1)))]
    · have hd := (rotateConfig config i.castSucc).dist_le_one hp (anchors h.cover i)
      have hf := rectangle_anchor_far hx hY i hi2 hi3 hi4
      nlinarith [dist_nonneg (x:=point x (h₀*Y)) (y:=vertex i)]
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (covered h.cover hex)
  fin_cases i
  · exact (outer 0 (by decide) (by decide) hi).elim
  · exact (outer 1 (by decide) (by decide) hi).elim
  · exact Or.inl hi
  · exact Or.inr hi
  · exact (outer 4 (by decide) (by decide) hi).elim
  · exact (outer 5 (by decide) (by decide) hi).elim
  · exact (central hi).elim

#print axioms actual_lower_rectangle

end
end HexagonCover.E4InsideRegion
