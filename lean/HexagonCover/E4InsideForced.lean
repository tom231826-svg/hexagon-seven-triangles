import HexagonCover.GapForcedPoint
import HexagonCover.SoleGapArea

/-! Source-exposed sole-E4 central duty D. Every exclusion concerns the
same normalized configuration. No A-in-T2 premise or independent central pose
is introduced. The finite heavy-depth estimate excludes all of actual T5. -/
namespace HexagonCover.E4InsideForced
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def D : Plane := point (3/5) (7*h₀/15)

theorem D_interior_hexagon : D∈interior (Hexagon 1) := by
  let q : Plane := (11/25:ℝ) • hexVertex 1 0+(14/25:ℝ) • hexVertex 1 1
  have hq : q∈Hexagon 1 := (convex_hexagon 1) (hexVertex_mem 1 0) (hexVertex_mem 1 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hz : (0:Plane)∈interior (Hexagon 1) := zero_mem_interior_hexagon (by norm_num)
  have hp := (convex_hexagon 1).combo_interior_self_mem_interior hz hq
    (a:=(1/6:ℝ)) (b:=(5/6:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have he : (1/6:ℝ) • (0:Plane)+(5/6:ℝ) • q=D := by
    ext i
    fin_cases i <;> simp [q,D,hexVertex,NICertificate.halfRoot] <;> ring
  exact he ▸ hp

theorem exclude_by_point (T : UnitTriangle) {p : Plane} (hp : p∈T.region)
    (hfar : 1 < (dist D p)^2) : D∉T.region := by
  intro hD
  have hd := T.dist_le_one hD hp
  have hs : (dist D p)^2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr hd
  linarith

theorem fixed_anchor_far (i : Fin 6) (hi0 : i≠0) (hi5 : i≠5) :
    1 < (dist D (vertex i))^2 := by
  fin_cases i
  all_goals try exact (hi0 rfl).elim
  all_goals try exact (hi5 rfl).elim
  all_goals norm_num [D,vertex_table,dist_point_sq]
  all_goals nlinarith [ExtremeTriangle.halfRoot_sq]

theorem zero_far {v : ℝ} (hv : 4/5 < v) : 1 < (dist D (point (1/2-v) h₀))^2 := by
  rw [D,dist_point_sq]
  nlinarith [ExtremeTriangle.halfRoot_sq,sq_nonneg (v-4/5)]

theorem D_depth : HeavyDepth.upperDepth D=h₀/6 := by
  unfold HeavyDepth.upperDepth D
  norm_num
  ring

theorem outer_exclusion {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (hM : 23/25 < M h) (hb0 : 4/5 < b h.cover 0) :
    ∀i:Fin 6,D∉(rotateConfig config i.castSucc).region := by
  intro i
  by_cases hi0 : i=0
  · subst i
    exact exclude_by_point _ (GapForcedPoint.zero_endpoint h) (zero_far hb0)
  by_cases hi5 : i=5
  · subst i
    intro hp
    have hd := HeavyDepthTransport.actual_source_depth h (by linarith) D hp
    rw [D_depth] at hd
    have hW := HeavyDepth.W_lt_thirtytwo hM
    have hcompare : 32*h₀/193 < h₀/6 := by nlinarith [ExtremeTriangle.halfRoot_pos]
    linarith
  exact exclude_by_point _ (anchors h.cover i) (fixed_anchor_far i hi0 hi5)

theorem same_central_interior_of_bounds {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (hM : 23/25 < M h) (hb0 : 4/5 < b h.cover 0) :
    D∈interior (rotateConfig config 6).region := by
  let outer : Set Plane := ⋃i:Fin 6,(rotateConfig config i.castSucc).region
  have hclosed : IsClosed outer := isClosed_iUnion_of_finite
    (fun i : Fin 6 => (rotateConfig config i.castSucc).closed_region)
  have hopen : IsOpen (interior (Hexagon 1) \ outer) := isOpen_interior.sdiff hclosed
  have hD : D∈interior (Hexagon 1) \ outer := by
    refine ⟨D_interior_hexagon,?_⟩
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

/-- The same actual positive-gap family supplies every numeric premise. -/
theorem same_central_interior {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    D∈interior (rotateConfig config 6).region :=
  same_central_interior_of_bounds h
    (GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩)
    (SoleGapArea.b0_four_fifths h sole)

theorem same_central {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    D∈(rotateConfig config 6).region := interior_subset (same_central_interior h sole)

#print axioms same_central_interior

end
end HexagonCover.E4InsideForced
