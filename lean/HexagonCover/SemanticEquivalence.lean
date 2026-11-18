import HexagonCover.Symmetry
import HexagonCover.Configuration

/-! Exact shape and coverage adapters for the final statement audit.
The target's UnitTriangle type is equivalent, at the level of its full closed
region, to an arbitrary translation and proper rotation of one standard
equilateral triangle. Arbitrary global poses of the hexagon are pulled back
using the same isometry on every one of the seven actual pieces. -/
namespace HexagonCover.SemanticEquivalence
noncomputable section
open RigidMotion Symmetry

theorem standard_region_eq_fan_zero : standardRegion = (StandardCover.fan 0).region := by
  have hv : standardVertices = (StandardCover.fan 0).vertex := by
    funext i
    fin_cases i <;> simp [standardVertices,StandardCover.fan,StandardCover.fanVertices,
      hexVertex,NICertificate.halfRoot]
  change convexHull ℝ (Set.range standardVertices) =
    convexHull ℝ (Set.range (StandardCover.fan 0).vertex)
  rw [hv]

/-- Every translated proper rotation is represented by an actual UnitTriangle. -/
theorem rigid_image_is_triangle (a : Plane) (c d : ℝ) (hu : c^2+d^2=1) :
    ∃ T : UnitTriangle,T.region=rigid a c d hu '' standardRegion := by
  refine ⟨mapTriangle (rigid a c d hu) (StandardCover.fan 0),?_⟩
  rw [map_region,standard_region_eq_fan_zero]

/-- Two directions of the geometric specification, not merely a one-way
soundness inclusion. Vertex relabelling is immaterial to a closed region. -/
theorem region_iff_rigid_image (S : Set Plane) :
    (∃ T : UnitTriangle,S=T.region) ↔
      ∃ a : Plane,∃ c d : ℝ,∃ hu : c^2+d^2=1,
        S=rigid a c d hu '' standardRegion := by
  constructor
  · rintro ⟨T,rfl⟩
    exact exists_region_rigid_motion T
  · rintro ⟨a,c,d,hu,hS⟩
    obtain ⟨T,hT⟩ := rigid_image_is_triangle a c d hu
    exact ⟨T,hS.trans hT.symm⟩

theorem triangle_vertices_injective (T : UnitTriangle) : Function.Injective T.vertex := by
  intro i j he
  by_contra hn
  have hd := T.edgeLength i j hn
  rw [he,dist_self] at hd
  norm_num at hd

/-- `s` is side length, not diameter or inradius. -/
theorem hexagon_adjacent_distance {s : ℝ} (hs : 0 ≤ s) (i : Fin 6) :
    dist (hexVertex s i) (hexVertex s (i+1))=s := by
  rw [hexVertex_smul s i,hexVertex_smul s (i+1),dist_eq_norm,←smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg hs,←dist_eq_norm,Configuration.adjacent_distance]
  ring

theorem hexagon_vertices_injective {s : ℝ} (hs : 0 < s) :
    Function.Injective (hexVertex s) := by
  intro i j he
  by_contra hn
  have hd := hexVertex_dist_sq_lower s i j hn
  rw [he,dist_self] at hd
  nlinarith [sq_pos_of_pos hs]

theorem hexagon_closed (s : ℝ) : IsClosed (Hexagon s) :=
  (compact_hexagon s).isClosed

/-- Coverage of an arbitrarily moved covered set is exactly coverage by
pulling back all seven of the same actual pieces. No separation, placement,
orientation, containment or distinctness assumption is added. -/
theorem coverage_image_iff (f : Plane ≃ᵃⁱ[ℝ] Plane) (S : Set Plane)
    (config : Fin 7 → UnitTriangle) :
    f '' S ⊆ ⋃i,(config i).region ↔
      S ⊆ ⋃i,(mapTriangle f.symm (config i)).region := by
  constructor
  · intro hc x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hc ⟨x,hx,rfl⟩)
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [map_region]
    exact ⟨f x,hi,f.symm_apply_apply x⟩
  · intro hc y hy
    obtain ⟨x,hx,rfl⟩ := hy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hc hx)
    rw [map_region] at hi
    obtain ⟨z,hz,hzx⟩ := hi
    have he : z=f x := by simpa only [f.apply_symm_apply] using congrArg f hzx
    exact Set.mem_iUnion.mpr ⟨i,by rwa [←he]⟩

theorem moved_hexagon_cover_iff (f : Plane ≃ᵃⁱ[ℝ] Plane) (s : ℝ)
    (config : Fin 7 → UnitTriangle) :
    f '' Hexagon s ⊆ ⋃i,(config i).region ↔
      Covers s (fun i=>mapTriangle f.symm (config i)) :=
  coverage_image_iff f (Hexagon s) config

/-- The endpoint s=1 remains feasible, with a permitted repeated seventh piece. -/
theorem boundary_sanity : ∃ config : Fin 7 → UnitTriangle,Covers 1 config :=
  StandardCover.exists_unit_hexagon_cover

#print axioms region_iff_rigid_image
#print axioms hexagon_adjacent_distance
#print axioms hexagon_vertices_injective
#print axioms hexagon_closed
#print axioms moved_hexagon_cover_iff
#print axioms boundary_sanity
end
end HexagonCover.SemanticEquivalence
