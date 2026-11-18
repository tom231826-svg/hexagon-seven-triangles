import HexagonCover.HeavyDepthTransport

/-! Source-exposed b3-Gs section2: the fixed actual point R belongs to the same
central triangle. All six outer exclusions use the same source-coordinate
configuration, its real anchors, real endpoint b0, and whole finite heavy depth. -/
namespace HexagonCover.GapForcedPoint
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def R : Plane := point (7/10) (h₀/7)

theorem R_interior_hexagon : R∈interior (Hexagon 1) := by
  let q : Plane := (22/27:ℝ) • hexVertex 1 0+(5/27:ℝ) • hexVertex 1 1
  have hq : q∈Hexagon 1 := (convex_hexagon 1) (hexVertex_mem 1 0) (hexVertex_mem 1 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hz : (0:Plane)∈interior (Hexagon 1) := zero_mem_interior_hexagon (by norm_num)
  have hp := (convex_hexagon 1).combo_interior_self_mem_interior hz hq
    (a:=(8/35:ℝ)) (b:=(27/35:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have he : (8/35:ℝ) • (0:Plane)+(27/35:ℝ) • q=R := by
    ext i
    fin_cases i <;> simp [q,R,hexVertex,NICertificate.halfRoot] <;> ring
  exact he ▸ hp

theorem exclude_by_point (T : UnitTriangle) {p : Plane} (hp : p∈T.region)
    (hfar : 1 < (dist R p)^2) : R∉T.region := by
  intro hR
  have hd := T.dist_le_one hR hp
  have hs : (dist R p)^2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr hd
  linarith

theorem fixed_anchor_far (i : Fin 6) (hi0 : i≠0) (hi5 : i≠5) :
    1 < (dist R (vertex i))^2 := by
  fin_cases i
  all_goals try exact (hi0 rfl).elim
  all_goals try exact (hi5 rfl).elim
  all_goals norm_num [R,vertex_table,dist_point_sq]
  all_goals nlinarith [ExtremeTriangle.halfRoot_sq]

theorem zero_endpoint {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    point (1/2-b h.cover 0) h₀ ∈ (rotateConfig config 0).region := by
  have hm := right_endpoint h.cover 0
    ⟨(rightReach h.cover 0).positive.le,(rightReach h.cover 0).lt_one.le⟩ le_rfl
  have he : AffineMap.lineMap (vertex 0) (vertex ((0:Fin 6)+1)) (b h.cover 0)=
      point (1/2-b h.cover 0) h₀ := by
    ext i
    fin_cases i <;> simp [vertex_table,AffineMap.lineMap_apply] <;> ring
  change AffineMap.lineMap (vertex 0) (vertex ((0:Fin 6)+1)) (b h.cover 0)∈
    (rotateConfig config 0).region at hm
  rwa [he] at hm

theorem zero_far {v : ℝ} (hv : 1/2 < v) : 1 < (dist R (point (1/2-v) h₀))^2 := by
  rw [R,dist_point_sq]
  nlinarith [ExtremeTriangle.halfRoot_sq,sq_nonneg (v-1/2)]

theorem R_depth : HeavyDepth.upperDepth R=8*h₀/35 := by
  unfold HeavyDepth.upperDepth R
  norm_num
  ring

/-- All outer misses are strict, and concern the same actual rotated pieces. -/
theorem outer_exclusion {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (hM : 9/10 < M h) (hb0 : 1/2 < b h.cover 0) :
    ∀i:Fin 6,R∉(rotateConfig config i.castSucc).region := by
  intro i
  by_cases hi0 : i=0
  · subst i
    exact exclude_by_point _ (zero_endpoint h) (zero_far hb0)
  by_cases hi5 : i=5
  · subst i
    intro hp
    have hd := HeavyDepthTransport.actual_source_depth h (by linarith) R hp
    rw [R_depth] at hd
    have hW := HeavyDepth.W_lt_nineteen hM
    have hcompare : 19*h₀/91 < 8*h₀/35 := by nlinarith [ExtremeTriangle.halfRoot_pos]
    linarith
  exact exclude_by_point _ (anchors h.cover i) (fixed_anchor_far i hi0 hi5)

/-- Closedness of all six actual outers upgrades the forced point to the
interior of the same central piece, with no uniform neighborhood radius. -/
theorem same_central_interior {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (hM : 9/10 < M h) (hb0 : 1/2 < b h.cover 0) :
    R∈interior (rotateConfig config 6).region := by
  let outer : Set Plane := ⋃i:Fin 6,(rotateConfig config i.castSucc).region
  have hclosed : IsClosed outer := isClosed_iUnion_of_finite
    (fun i : Fin 6 => (rotateConfig config i.castSucc).closed_region)
  have hopen : IsOpen (interior (Hexagon 1) \ outer) := isOpen_interior.sdiff hclosed
  have hR : R∈interior (Hexagon 1) \ outer := by
    refine ⟨R_interior_hexagon,?_⟩
    intro hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact outer_exclusion h hM hb0 i hi
  have hsubset : interior (Hexagon 1) \ outer ⊆ (rotateConfig config 6).region := by
    intro p hp
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (covered h.cover (interior_subset hp.1))
    by_cases he : j=6
    · simpa only [he] using hj
    · have hjlt : j.val < 6 := by omega
      let i : Fin 6 := ⟨j.val,hjlt⟩
      have hij : i.castSucc=j := by ext; rfl
      exact (hp.2 (Set.mem_iUnion.mpr ⟨i,by simpa only [hij] using hj⟩)).elim
  apply interior_mono hsubset
  rwa [hopen.interior_eq]

theorem same_central {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (hM : 9/10 < M h) (hb0 : 1/2 < b h.cover 0) :
    R∈(rotateConfig config 6).region :=
  interior_subset (same_central_interior h hM hb0)

end
end HexagonCover.GapForcedPoint
