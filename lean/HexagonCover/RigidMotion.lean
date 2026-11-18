import HexagonCover.TriangleFrame

/-!
# Actual equilateral triangles are translated proper rotations

The standard triangle has vertices `(0,0)`, `(1,0)`, and `(1/2,sqrt 3/2)`.
Relabelling the actual vertices absorbs the possible reversal of orientation.
-/

namespace HexagonCover.RigidMotion

noncomputable section

open TriangleFrame

private theorem eta (p : Plane) : point (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

/-- The coordinate matrix is `[[c,-d],[d,c]]`. -/
def rotation (c d : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := point (c * p 0 - d * p 1) (d * p 0 + c * p 1)
  map_add' p q := by ext i; fin_cases i <;> simp [point] <;> ring
  map_smul' a p := by ext i; fin_cases i <;> simp [point] <;> ring

@[simp] theorem rotation_apply (c d : ℝ) (p : Plane) :
    rotation c d p = point (c * p 0 - d * p 1) (d * p 0 + c * p 1) := rfl

theorem rotation_norm {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) (p : Plane) :
    ‖rotation c d p‖ = ‖p‖ := by
  have hp := norm_point_sq (p 0) (p 1)
  rw [eta] at hp
  have hr := norm_point_sq (c * p 0 - d * p 1) (d * p 0 + c * p 1)
  change ‖rotation c d p‖ ^ 2 = _ at hr
  have hm := congrArg (fun x : ℝ => x * (p 0 ^ 2 + p 1 ^ 2)) hu
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith

theorem rotation_inverse {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) (p : Plane) :
    rotation c (-d) (rotation c d p) = p := by
  ext i
  fin_cases i <;> simp [rotation]
  all_goals nlinarith [congrArg (fun x : ℝ => x * p 0) hu,
    congrArg (fun x : ℝ => x * p 1) hu]

def rotationEquiv (c d : ℝ) (hu : c ^ 2 + d ^ 2 = 1) : Plane ≃ₗ[ℝ] Plane where
  toLinearMap := rotation c d
  invFun := rotation c (-d)
  left_inv := rotation_inverse hu
  right_inv p := by
    simpa using rotation_inverse (c := c) (d := -d) (by simpa using hu) p

def rotationIsometry (c d : ℝ) (hu : c ^ 2 + d ^ 2 = 1) : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv := rotationEquiv c d hu
  norm_map' := rotation_norm hu

/-- The explicit rotation matrix has determinant positive one. -/
theorem rotation_matrix_det {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) :
    Matrix.det !![c, -d; d, c] = 1 := by
  norm_num [Matrix.det_fin_two]
  nlinarith

theorem rotation_toMatrix (c d : ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (rotation c d) = !![c, -d; d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, rotation]

/-- Proper orientation of the actual linear map, not just an auxiliary matrix. -/
theorem rotation_det {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) :
    LinearMap.det (rotation c d) = 1 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    rotation_toMatrix]
  exact rotation_matrix_det hu

/-- Translation followed by an orientation-preserving linear isometry. -/
def rigid (a : Plane) (c d : ℝ) (hu : c ^ 2 + d ^ 2 = 1) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rotationIsometry c d hu).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ Plane a)

@[simp] theorem rigid_apply (a : Plane) (c d : ℝ) (hu : c ^ 2 + d ^ 2 = 1) (p : Plane) :
    rigid a c d hu p = a + rotation c d p := rfl

def standardVertices : Fin 3 → Plane :=
  ![0, point 1 0, point (1 / 2) NICertificate.halfRoot]

def standardRegion : Set Plane := convexHull ℝ (Set.range standardVertices)

/-- Rotation by sixty degrees, applied to an edge vector. -/
def turn60 : Plane →ₗ[ℝ] Plane :=
  (1 / 2 : ℝ) • LinearMap.id + NICertificate.halfRoot • rotation 0 1

theorem normal_sub (T : UnitTriangle) (i j : Fin 3) :
    normal T i - normal T j = (-Real.sqrt 3) • (T.vertex i - T.vertex j) := by
  unfold normal centered
  module

theorem chart_third_edge (T : UnitTriangle) (c d : ℝ) (σ : Equiv.Perm (Fin 3))
    (hn : ∀ i, ((normal T (σ i)) 0, (normal T (σ i)) 1) =
      NICertificate.normalValues c d i) :
    T.vertex (σ 2) - T.vertex (σ 0) = turn60 (T.vertex (σ 1) - T.vertex (σ 0)) := by
  have hv (i : Fin 3) : normal T (σ i) =
      point (NICertificate.normalValues c d i).1 (NICertificate.normalValues c d i).2 := by
    rw [← hn i]
    exact (eta _).symm
  have he : normal T (σ 2) - normal T (σ 0) =
      turn60 (normal T (σ 1) - normal T (σ 0)) := by
    rw [hv 0, hv 1, hv 2]
    ext i
    fin_cases i <;> simp [turn60, rotation, NICertificate.normalValues]
    all_goals nlinarith [congrArg (fun x : ℝ => x * c) ExtremeTriangle.halfRoot_sq,
      congrArg (fun x : ℝ => x * d) ExtremeTriangle.halfRoot_sq]
  rw [normal_sub, normal_sub, map_smul] at he
  exact smul_right_injective Plane
    (neg_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))) he

/-- The three actual vertices are a relabelled translated proper rotation of
all three standard vertices. -/
theorem exists_vertex_rigid_motion (T : UnitTriangle) :
    ∃ a : Plane, ∃ c d : ℝ, ∃ hu : c ^ 2 + d ^ 2 = 1, ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, rigid a c d hu (standardVertices i) = T.vertex (σ i) := by
  obtain ⟨u, v, σ, _, _, hn⟩ := normal_chart T
  let a := T.vertex (σ 0)
  let e := T.vertex (σ 1) - T.vertex (σ 0)
  have hu : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hd := dist_sq_coordinates (T.vertex (σ 1)) (T.vertex (σ 0))
    rw [T.edgeLength _ _ (σ.injective.ne (by decide))] at hd
    simpa [e] using hd.symm
  have he := chart_third_edge T u v σ hn
  refine ⟨a, e 0, e 1, hu, σ, ?_⟩
  intro i
  fin_cases i
  · simp [rigid_apply, standardVertices, a]
  · change a + rotation (e 0) (e 1) (point 1 0) = T.vertex (σ 1)
    have hrot : rotation (e 0) (e 1) (point 1 0) = e := by simp [rotation, eta]
    rw [hrot]
    dsimp [a, e]
    abel
  · change rigid a (e 0) (e 1) hu (standardVertices 2) = T.vertex (σ 2)
    have hrot : rotation (e 0) (e 1) (standardVertices 2) = turn60 e := by
      ext j
      fin_cases j <;> simp [standardVertices, rotation, turn60] <;> ring
    rw [rigid_apply, hrot, ← he]
    dsimp [a]
    abel

/-- Exact equivalence between the actual closed triangular region and a
translated proper rotation of the canonical closed triangle. -/
theorem exists_region_rigid_motion (T : UnitTriangle) :
    ∃ a : Plane, ∃ c d : ℝ, ∃ hu : c ^ 2 + d ^ 2 = 1,
      T.region = rigid a c d hu '' standardRegion := by
  obtain ⟨a, c, d, hu, σ, hverts⟩ := exists_vertex_rigid_motion T
  refine ⟨a, c, d, hu, ?_⟩
  have hrange : rigid a c d hu '' Set.range standardVertices = Set.range T.vertex := by
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨σ i, (hverts i).symm⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := σ.surjective i
      exact ⟨standardVertices j, ⟨j, rfl⟩, hverts j⟩
  change convexHull ℝ (Set.range T.vertex) =
    rigid a c d hu '' convexHull ℝ (Set.range standardVertices)
  have hi := (rigid a c d hu).toAffineEquiv.toAffineMap.image_convexHull
    (Set.range standardVertices)
  change rigid a c d hu '' convexHull ℝ (Set.range standardVertices) =
    convexHull ℝ (rigid a c d hu '' Set.range standardVertices) at hi
  rw [hrange] at hi
  exact hi.symm

end
end HexagonCover.RigidMotion
