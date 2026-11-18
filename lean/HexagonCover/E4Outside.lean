import HexagonCover.E4StrictAxis
import HexagonCover.SoleOutsidePacket
import HexagonCover.SoleGapAxis
import HexagonCover.SoleGapArea

/-! Source-exposed A-outside-T2 branch. Every membership below belongs to the
same actual rotated configuration. The final implication uses no supplied
packet-membership assumptions. -/
namespace HexagonCover.E4Outside
noncomputable section
open HexagonCover.Configuration NormalizedHeavy BoundaryGaps SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def A : Plane := point (-19/100) 0

theorem source_anchor_ball {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) : ∃r>0,Metric.ball (vertex i) r ⊆ (rotateConfig config i.castSucc).region := by
  obtain ⟨r,hr,hb⟩ := h.anchorBalls i.castSucc
  rw [qAnchor_outer] at hb
  have hm := CornerTransport.action_ball QSymmetry.rotationAction
    (config i.castSucc) (hexVertex 1 i) hb
  change Metric.ball (Symmetry.turn (hexVertex 1 i)) r ⊆
    (rotateConfig config i.castSucc).region at hm
  rw [turn_vertex_eq] at hm
  exact ⟨r,hr,hm⟩

theorem axis_not_three {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) {z : ℝ} (hz : 0 < z) (hz' : z < 1/4) :
    point (-z) 0∉(rotateConfig config 3).region := by
  obtain ⟨r,hr,hball⟩ := source_anchor_ball h.cover 3
  have hb := (SoleGapArea.light_reach_order h sole 3).2
  have hm := right_endpoint h.cover 3 (t:=1/2) (by norm_num) (by simpa using hb.le)
  have he : AffineMap.lineMap (vertex 3) (vertex ((3:Fin 6)+1)) (1/2:ℝ)=
      vertex 3+point (1/2) 0 := by
    ext i
    fin_cases i <;> norm_num [vertex_table,AffineMap.lineMap_apply,point]
  rw [he] at hm
  have hx := E4StrictAxis.translated_exclusion hz hz' (rotateConfig config 3)
    (vertex 3) hr hball hm
  have he' : vertex 3+point (1/2-z) h₀=point (-z) 0 := by
    ext i
    fin_cases i <;> norm_num [vertex_table,point] <;> ring
  rwa [he'] at hx

theorem exclude_far (T : UnitTriangle) {p q : Plane} (hq : q∈T.region)
    (hfar : 1 < (dist p q)^2) : p∉T.region := by
  intro hp
  have hd := T.dist_le_one hp hq
  have hs : (dist p q)^2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ)≤1)).mpr hd
  linarith

theorem axis_not_zero_four {config : Fin 7 → UnitTriangle} (h : Normalized config)
    {z : ℝ} (hz : 0 < z) (i : Fin 6) (hi : i=0 ∨ i=4) :
    point (-z) 0∉(rotateConfig config i.castSucc).region := by
  apply exclude_far _ (anchors h.cover i)
  rcases hi with rfl | rfl
  all_goals norm_num [vertex_table,dist_point_sq]
  all_goals nlinarith [ExtremeTriangle.halfRoot_sq,sq_nonneg z]

theorem axis_not_five {config : Fin 7 → UnitTriangle} (h : Normalized config)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1/2) :
    point (-z) 0∉(rotateConfig config 5).region := by
  intro hp
  have hn := SourceCoordinates.separation (config:=config) 5 (structure_bounds h).2.2.2.2.2
    (point (-z) 0) hp
  have he : ‖point (-z) 0‖=z := by
    have hs := norm_point_sq (-z) 0
    nlinarith [norm_nonneg (point (-z) 0)]
  rw [he] at hn
  linarith

theorem axis_hex {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) : point (-z) 0∈Hexagon 1 := by
  have hm := (convex_hexagon 1) (hexVertex_mem 1 3)
    (interior_subset (zero_mem_interior_hexagon (by norm_num : (0:ℝ)<1)))
    hz (sub_nonneg.mpr hz') (show z+(1-z)=1 by ring)
  have he : z • hexVertex 1 3+(1-z) • (0:Plane)=point (-z) 0 := by
    ext i
    fin_cases i <;> simp [hexVertex,point]
  exact he ▸ hm

theorem axis_forced_one {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) {z : ℝ} (hz : 0 < z) (hz' : z < 1/4)
    (h2 : point (-z) 0∉(rotateConfig config 2).region)
    (h6 : point (-z) 0∉(rotateConfig config 6).region) :
    point (-z) 0∈(rotateConfig config 1).region := by
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (covered h.cover (axis_hex hz.le (by linarith)))
  fin_cases i
  · exact (axis_not_zero_four h hz 0 (Or.inl rfl) hi).elim
  · exact hi
  · exact (h2 hi).elim
  · exact (axis_not_three h sole hz hz' hi).elim
  · exact (axis_not_zero_four h hz 4 (Or.inr rfl) hi).elim
  · exact (axis_not_five h hz.le (by linarith) hi).elim
  · exact (h6 hi).elim

theorem axis_not_central {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (gap4 : gap h.cover 4) {z : ℝ} (hz : a h.cover 5/2 ≤ z) :
    point (-z) 0∉(rotateConfig config 6).region := by
  apply exclude_far _ (CentralAxis.source_P_mem h gap4)
  have ha : 0 < a h.cover 5 := (leftReach h.cover 5).positive
  have he : CentralAxis.P (a h.cover 5)=point (1-a h.cover 5/2) (-h₀*a h.cover 5) := by
    ext i
    fin_cases i <;> simp [CentralAxis.P,ExteriorLoss.lowerEndpoint,ExteriorLoss.corner,
      ExteriorLoss.lowerRay,point] <;> ring
  rw [he,dist_point_sq]
  have hh := ExtremeTriangle.halfRoot_sq
  calc
    1 < 1+2*(z-a h.cover 5/2)+(z-a h.cover 5/2)^2+(3/4)*(a h.cover 5)^2 := by
      nlinarith [sq_pos_of_pos ha,sq_nonneg (z-a h.cover 5/2)]
    _ = _ := by nlinarith only [congrArg (fun x:ℝ => x*(a h.cover 5)^2) hh]

theorem axis_convex_transfer (T : UnitTriangle) {w : ℝ} (hw : 0 < w)
    (hw' : w < 2/25) (hanchor : point (-1) 0∈T.region)
    (hQ : point (-w) 0∈T.region) : A∈T.region := by
  have hd : 0 < 1-w := by linarith
  have hq0 : 0 ≤ (81/100:ℝ)/(1-w) := div_nonneg (by norm_num) hd.le
  have hq1 : (81/100:ℝ)/(1-w) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hm := T.convex_region hanchor hQ (sub_nonneg.mpr hq1) hq0
    (show 1-(81/100:ℝ)/(1-w)+(81/100:ℝ)/(1-w)=1 by ring)
  have he : (1-(81/100:ℝ)/(1-w)) • point (-1) 0+
      ((81/100:ℝ)/(1-w)) • point (-w) 0=A := by
    ext i
    fin_cases i <;> simp [A,point]
    all_goals field_simp [ne_of_gt hd] <;> ring
  exact he ▸ hm

/-- The entire outside branch is impossible; the remaining branch includes
every contact of A with the closed actual triangle T2. -/
theorem A_mem_two {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) : A∈(rotateConfig config 2).region := by
  by_contra hA2
  have hg : gap h.cover 4 := (sole 4).mpr rfl
  have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,hg⟩
  have ha : 0 < a h.cover 5 := (leftReach h.cover 5).positive
  have hshort := GapChains.heavy_short h
  let w := a h.cover 5/2
  have hw : 0 < w := by dsimp [w]; linarith
  have hw' : w < 2/25 := by dsimp [w]; linarith
  have hA1 : A∈(rotateConfig config 1).region := by
    have h2 : point (-(19/100:ℝ)) 0∉(rotateConfig config 2).region := by simpa [A,neg_div] using hA2
    have h1 := axis_forced_one h sole (z:=19/100) (by norm_num) (by norm_num) h2
      (axis_not_central h hg (by change w ≤ 19/100; linarith))
    simpa [A,neg_div] using h1
  have hQ2 : point (-w) 0∉(rotateConfig config 2).region := by
    intro hQ
    apply hA2
    apply axis_convex_transfer _ hw hw' ?_ hQ
    have hx := anchors h.cover (2:Fin 6)
    norm_num [vertex_table] at hx
    exact hx
  have hQ1 := axis_forced_one h sole hw (by linarith) hQ2 (axis_not_central h hg le_rfl)
  have hwle : w ≤ a h.cover 1 := by
    have hl := (structure_bounds h).1 1
    have hla := hl.trans (min_le_left _ _)
    dsimp [w]
    linarith
  have hP := left_endpoint h.cover 1 (t:=w) ⟨hw.le,by linarith⟩ hwle
  have hPe : AffineMap.lineMap (vertex 1) (vertex ((1:Fin 6)-1)) w=
      vertex 1+point w 0 := by
    ext i
    fin_cases i <;> simp [vertex_table,AffineMap.lineMap_apply,point] <;> ring
  rw [hPe] at hP
  apply SoleOutsidePacket.impossible hw hw' (E4StrictAxis.shiftTriangle (rotateConfig config 1) (vertex 1))
  intro i
  have hm : vertex 1+SoleOutsidePacket.points w i∈(rotateConfig config 1).region := by
    fin_cases i
    · simpa [SoleOutsidePacket.points] using anchors h.cover 1
    · convert hA1 using 1 <;> ext j <;> fin_cases j <;>
        norm_num [vertex_table,SoleOutsidePacket.points,A,point]
    · convert hQ1 using 1 <;> ext j <;> fin_cases j <;>
        simp [vertex_table,SoleOutsidePacket.points,point] <;> ring
    · exact hP
  have hs := (E4StrictAxis.mem_shift _ (vertex 1) (vertex 1+SoleOutsidePacket.points w i)).mpr hm
  simpa only [add_sub_cancel_left] using hs

#print axioms A_mem_two
end
end HexagonCover.E4Outside
