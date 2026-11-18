import HexagonCover.DistanceLeaf

/-!+Strict point/segment intrusion into an open disk. All executable checks use
rational pairs. In the segment proof the real parameter is the exact quotient
`d/E`, not a rational approximation. Boundary equality never closes a leaf.
-/

namespace HexagonCover.PointSegmentLeaf

open Quadratic3 DistanceLeaf

def normSquared (p : ExactPoint) : Number := add (square p.x) (square p.y)

def dotExact (p q : ExactPoint) : Number := add (mul p.x q.x) (mul p.y q.y)

def delta (p q : ExactPoint) : ExactPoint := ⟨sub q.x p.x, sub q.y p.y⟩

def energy (p q : ExactPoint) : Number := normSquared (delta p q)

def projection (p q : ExactPoint) : Number := neg (dotExact p (delta p q))

def gap (p q : ExactPoint) (radiusSquared : Number) : Number :=
  add (mul (sub radiusSquared (normSquared p)) (energy p q)) (square (projection p q))

def pointCheck (p : ExactPoint) (radiusSquared : Number) : Bool :=
  positive radiusSquared && positive (sub radiusSquared (normSquared p))

def segmentCheck (p q : ExactPoint) (radiusSquared : Number) : Bool :=
  positive radiusSquared &&
    (positive (energy p q) &&
      (positive (projection p q) &&
        (positive (sub (energy p q) (projection p q)) && positive (gap p q radiusSquared))))

@[simp] theorem normSquared_real (p : ExactPoint) :
    real (normSquared p) = ‖toPlane p‖ ^ 2 := by
  simp only [normSquared, real_add, real_square, toPlane, norm_point_sq]

theorem pointCheck_sound {p : ExactPoint} {r : Number} (accepted : pointCheck p r = true) :
    0 < real r ∧ ‖toPlane p‖ ^ 2 < real r := by
  obtain ⟨hr, hp⟩ := Bool.and_eq_true_iff.mp accepted
  have h := positive_sound _ hp
  rw [real_sub, normSquared_real] at h
  exact ⟨positive_sound _ hr, by linarith⟩

/-- Scalar algebra for the exact closest point in the interior of a segment. -/
theorem segment_algebra (ax ay ex ey r : ℝ)
    (hE : 0 < ex ^ 2 + ey ^ 2)
    (hd : 0 < -(ax * ex + ay * ey))
    (hdE : -(ax * ex + ay * ey) < ex ^ 2 + ey ^ 2)
    (hgap : 0 < (r - (ax ^ 2 + ay ^ 2)) * (ex ^ 2 + ey ^ 2) +
      (-(ax * ex + ay * ey)) ^ 2) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (ax + t * ex) ^ 2 + (ay + t * ey) ^ 2 < r := by
  let t := -(ax * ex + ay * ey) / (ex ^ 2 + ey ^ 2)
  have ht0 : 0 < t := div_pos hd hE
  have ht1 : t < 1 := (div_lt_one hE).2 hdE
  have hEnz : ex ^ 2 + ey ^ 2 ≠ 0 := ne_of_gt hE
  have identity : ((ax + t * ex) ^ 2 + (ay + t * ey) ^ 2) * (ex ^ 2 + ey ^ 2) =
      (ax ^ 2 + ay ^ 2) * (ex ^ 2 + ey ^ 2) - (-(ax * ex + ay * ey)) ^ 2 := by
    dsimp [t]
    field_simp [hEnz]
    ring
  refine ⟨t, ht0, ht1, ?_⟩
  have hproduct : ((ax + t * ex) ^ 2 + (ay + t * ey) ^ 2) * (ex ^ 2 + ey ^ 2) <
      r * (ex ^ 2 + ey ^ 2) := by
    rw [identity]
    nlinarith only [hgap]
  exact lt_of_mul_lt_mul_right hproduct (le_of_lt hE)

/-- A successful segment check constructs a point of the actual closed triangle
whose squared norm is strictly less than the specified squared radius. -/
theorem segmentCheck_sound {p q : ExactPoint} {r : Number}
    (accepted : segmentCheck p q r = true) (T : UnitTriangle)
    (hp : toPlane p ∈ T.region) (hq : toPlane q ∈ T.region) :
    0 < real r ∧ ∃ z ∈ T.region, ‖z‖ ^ 2 < real r := by
  obtain ⟨hr, hrest⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨hEb, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hdb, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hdEb, hgapb⟩ := Bool.and_eq_true_iff.mp hrest
  have hE := positive_sound _ hEb
  have hd := positive_sound _ hdb
  have hdE := positive_sound _ hdEb
  have hgap := positive_sound _ hgapb
  simp only [energy, projection, gap, normSquared, dotExact, delta,
    real_add, real_sub, real_neg, real_mul, real_square] at hE hd hdE hgap
  have hdE' := sub_pos.mp hdE
  obtain ⟨t, ht0, ht1, hsmall⟩ := segment_algebra (real p.x) (real p.y)
    (real q.x - real p.x) (real q.y - real p.y) (real r) hE hd hdE' hgap
  let z : Plane := (1 - t) • toPlane p + t • toPlane q
  have hz : z ∈ T.region := T.convex_region hp hq (by linarith) (le_of_lt ht0) (by ring)
  have hz_eq : z = point (real p.x + t * (real q.x - real p.x))
      (real p.y + t * (real q.y - real p.y)) := by
    ext i
    fin_cases i <;> simp [z, toPlane, point] <;> ring
  refine ⟨positive_sound _ hr, z, hz, ?_⟩
  rw [hz_eq, norm_point_sq]
  exact hsmall

inductive Witness where
  | point (index : Nat)
  | segment (first second : Nat)
  deriving DecidableEq, Repr

/-- Checked indexing into the actual same-owner obligation list. -/
def check (points : List ExactPoint) (r : Number) : Witness → Bool
  | .point i => match points[i]? with
      | some p => pointCheck p r
      | none => false
  | .segment i j => match points[i]?, points[j]? with
      | some p, some q => segmentCheck p q r
      | _, _ => false

theorem check_sound {points : List ExactPoint} {r : Number} {w : Witness}
    (accepted : check points r w = true) (T : UnitTriangle)
    (contained : ∀ p, p ∈ points → toPlane p ∈ T.region) :
    0 < real r ∧ ∃ z ∈ T.region, ‖z‖ ^ 2 < real r := by
  cases w with
  | point i =>
      cases hp : points[i]? with
      | none => simp [check, hp] at accepted
      | some p =>
          have hcheck : pointCheck p r = true := by simpa [check, hp] using accepted
          obtain ⟨hr, hnorm⟩ := pointCheck_sound hcheck
          exact ⟨hr, toPlane p, contained p (List.mem_of_getElem? hp), hnorm⟩
  | segment i j =>
      cases hp : points[i]? with
      | none => simp [check, hp] at accepted
      | some p =>
          cases hq : points[j]? with
          | none => simp [check, hp, hq] at accepted
          | some q =>
              have hcheck : segmentCheck p q r = true := by simpa [check, hp, hq] using accepted
              exact segmentCheck_sound hcheck T
                (contained p (List.mem_of_getElem? hp)) (contained q (List.mem_of_getElem? hq))

/-- Avoidance of the open disk, written directly in squared-norm form.
Tangency is allowed because the comparison is non-strict. -/
def NonIntruding (T : UnitTriangle) (r : Number) : Prop :=
  ∀ z ∈ T.region, real r ≤ ‖z‖ ^ 2

theorem cannot_be_nonintruding {points : List ExactPoint} {r : Number} {w : Witness}
    (accepted : check points r w = true) (T : UnitTriangle)
    (contained : ∀ p, p ∈ points → toPlane p ∈ T.region) : ¬ NonIntruding T r := by
  intro hni
  obtain ⟨_, z, hz, hsmall⟩ := check_sound accepted T contained
  exact (not_lt_of_ge (hni z hz)) hsmall

end HexagonCover.PointSegmentLeaf
