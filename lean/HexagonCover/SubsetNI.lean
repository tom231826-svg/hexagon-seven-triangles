import HexagonCover.GenericNI

/-!
Each original angle cell may use three explicitly indexed points from its full
obligation. The original angle, kind, edge indices, weights, and squared radius
are retained. Every cell is recomputed on its selected list; no interval
monotonicity assertion or producer acceptance flag is assumed.
-/

namespace HexagonCover.SubsetNI

open DistanceLeaf NICertificate ExtremeTriangle

structure Cell (points : List ExactPoint) where
  original : Exact.Interval × GenericNI.LeafKind
  picks : Fin 3 → Fin points.length

def Cell.selected {points : List ExactPoint} (cell : Cell points) : List ExactPoint :=
  List.ofFn (fun i => points.get (cell.picks i))

theorem Cell.selected_nonempty {points : List ExactPoint} (cell : Cell points) :
    cell.selected ≠ [] := by
  intro h
  have hlength := congrArg List.length h
  simp [Cell.selected] at hlength

theorem Cell.selected_member {points : List ExactPoint} (cell : Cell points)
    (p : ExactPoint) (hp : p ∈ cell.selected) : p ∈ points := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact List.get_mem _ _

structure Certificate (points : List ExactPoint) where
  cells : List (Cell points)
  frontier : List Exact.Interval

/-- The exact original payload retained by this proof transformation. -/
def Certificate.forget {points : List ExactPoint} (cert : Certificate points) :
    GenericNI.Certificate := ⟨cert.cells.map Cell.original, cert.frontier⟩

def check (points : List ExactPoint) (radiusSquared : ℚ) (cert : Certificate points) : Bool :=
  !points.isEmpty && decide (0 < radiusSquared) && cert.frontier.isEmpty &&
    partitionFrom (-1) 1 (cert.cells.map (fun cell => cell.original.1)) &&
    cert.cells.all (fun cell => GenericNI.cellCheck cell.selected radiusSquared cell.original)

theorem empty_points_rejected (r : ℚ) (cert : Certificate []) : check [] r cert = false := by
  simp [check]

theorem nonpositive_radius_rejected (points : List ExactPoint) (r : ℚ)
    (cert : Certificate points) (hr : r ≤ 0) : check points r cert = false := by
  have h : ¬ 0 < r := not_lt.mpr hr
  simp [check, h]

theorem frontier_rejected (points : List ExactPoint) (r : ℚ) (cert : Certificate points)
    (hf : cert.frontier ≠ []) : check points r cert = false := by
  have h : cert.frontier.isEmpty = false := List.isEmpty_eq_false_iff.mpr hf
  simp [check, h]

theorem check_orientation {points : List ExactPoint} {r : ℚ} {cert : Certificate points}
    (accepted : check points r cert = true) (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    ∃ selected : List ExactPoint, selected ≠ [] ∧ (∀ p ∈ selected, p ∈ points) ∧
      GenericNI.OrientationExcluded selected r (NI.circleX t) (NI.circleY t) := by
  simp only [check, Bool.and_eq_true] at accepted
  rcases accepted with ⟨⟨⟨⟨_, _⟩, _⟩, hpartition⟩, hall⟩
  obtain ⟨I, hI, htI⟩ := partitionFrom_sound
    (cert.cells.map (fun cell => cell.original.1)) (-1) 1 hpartition
    (by norm_num) t (by simpa using ht)
  obtain ⟨cell, hcell, heq⟩ := List.mem_map.mp hI
  subst I
  refine ⟨cell.selected, cell.selected_nonempty, cell.selected_member, ?_⟩
  exact GenericNI.cellCheck_sound cell.selected r cell.original
    ((List.all_eq_true.mp hall) cell hcell) t htI

/-- Sound for the full original obligation and an actual arbitrary unit triangle.
The selected list can vary with the angle cell; no orientation premise is supplied. -/
theorem check_sound {points : List ExactPoint} {r : ℚ} {cert : Certificate points}
    (accepted : check points r cert = true) (T : UnitTriangle)
    (contained : ∀ p ∈ points, toPlane p ∈ T.region) :
    ∃ p ∈ T.region, ‖p‖ ^ 2 < (r : ℝ) := by
  obtain ⟨c, s, b, hc, hu, hsum, hmem⟩ := TriangleFrame.exists_normal_frame T
  obtain ⟨t, ht, hct, hst⟩ := NI.semicircle_parameterization hu hc
  obtain ⟨selected, hne, hsub, horient⟩ := check_orientation accepted t ht
  rw [hct, hst] at horient
  have hpoints : ∀ i p, p ∈ selected →
      dot (normalValues c s i) (GenericNI.pointValue p) ≤ b i := by
    intro i p hp
    have h := (hmem (toPlane p)).mp (contained p (hsub p hp)) i
    simpa only [toPlane, point_coord_zero, point_coord_one, GenericNI.pointValue] using h
  have hs : ∀ i, GenericNI.supportValue selected (normalValues c s i) ≤ b i := by
    intro i
    exact GenericNI.supportValue_upper selected hne _ _ (hpoints i)
  rcases horient with hgap | hext
  · exfalso
    linarith [hs 0, hs 1, hs 2]
  · obtain ⟨q, hq, hnorm⟩ := all_offsets_intersect_open_disk hs hsum hext
    refine ⟨point q.1 q.2, ?_, ?_⟩
    · apply (hmem _).mpr
      simpa only [point_coord_zero, point_coord_one, Prod.eta] using hq
    · rw [norm_point_sq]
      exact hnorm

theorem nonintrusion_impossible {points : List ExactPoint} {r : ℚ}
    {cert : Certificate points} (accepted : check points r cert = true) (T : UnitTriangle)
    (contained : ∀ p ∈ points, toPlane p ∈ T.region)
    (nonintrusion : ∀ p ∈ T.region, (r : ℝ) ≤ ‖p‖ ^ 2) : False := by
  obtain ⟨p, hp, hnorm⟩ := check_sound accepted T contained
  exact (not_le_of_gt hnorm) (nonintrusion p hp)

end HexagonCover.SubsetNI
