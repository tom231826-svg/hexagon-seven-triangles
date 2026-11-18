import HexagonCover.OrderedQuadratic3
import HexagonCover.DistanceLeaf
import HexagonCover.NICertificate

/-! Independent exact arithmetic for all point-pair support events.
No old convex-hull ordering or stored squared gap is trusted. The geometric
completeness wrapper is proved separately in SupportGeometry. -/
namespace HexagonCover.ExactSupport
open Quadratic3 DistanceLeaf

def negate (p : ExactPoint) : ExactPoint := ⟨neg p.x, neg p.y⟩
def difference (p q : ExactPoint) : ExactPoint := ⟨sub p.x q.x, sub p.y q.y⟩
def perpendicular (p : ExactPoint) : ExactPoint := ⟨neg p.y, p.x⟩
def dot (p q : ExactPoint) : Number := add (mul p.x q.x) (mul p.y q.y)
def halfRoot : Number := (0, 1/2)

def rotate (p : ExactPoint) : Fin 3 → ExactPoint
  | 0 => p
  | 1 => ⟨sub (mul (ofRat (-(1/2))) p.x) (mul halfRoot p.y),
      sub (mul halfRoot p.x) (mul (ofRat (1/2)) p.y)⟩
  | 2 => ⟨add (mul (ofRat (-(1/2))) p.x) (mul halfRoot p.y),
      sub (neg (mul halfRoot p.x)) (mul (ofRat (1/2)) p.y)⟩

def inverseRole : Fin 3 → Fin 3 := ![0, 2, 1]

def eventBase (p q : ExactPoint) (role : Fin 3) (negative : Bool) : ExactPoint :=
  let w := perpendicular (difference q p)
  rotate (if negative then negate w else w) (inverseRole role)

theorem real_dot (p q : ExactPoint) : real (dot p q) =
    (toPlane p) 0 * (toPlane q) 0 + (toPlane p) 1 * (toPlane q) 1 := by
  simp [dot, toPlane]

theorem real_halfRoot : real halfRoot = NICertificate.halfRoot := by
  norm_num [halfRoot, real, NICertificate.halfRoot]
  ring

theorem rotate_coordinates (p : ExactPoint) (i : Fin 3) :
    ((toPlane (rotate p i)) 0, (toPlane (rotate p i)) 1) =
      NICertificate.normalValues ((toPlane p) 0) ((toPlane p) 1) i := by
  fin_cases i <;> apply Prod.ext <;>
    simp [rotate, toPlane, NICertificate.normalValues, real_halfRoot] <;> ring

def foldSupport (points : List ExactPoint) (normal : ExactPoint) (seed : Number) : Number :=
  points.foldl (fun acc p => maximum acc (dot normal p)) seed

theorem foldSupport_le (points : List ExactPoint) (normal : ExactPoint) (seed : Number)
    (bound : ℝ) (hseed : real seed ≤ bound)
    (hpoints : ∀ p ∈ points, real (dot normal p) ≤ bound) :
    real (foldSupport points normal seed) ≤ bound := by
  induction points generalizing seed with
  | nil => exact hseed
  | cons p ps ih =>
      apply ih (maximum seed (dot normal p))
      · rw [real_maximum]
        exact max_le hseed (hpoints p (by simp))
      · intro q hq
        exact hpoints q (by simp [hq])

def support {n : ℕ} (points : Fin (n+1) → ExactPoint) (base : ExactPoint)
    (role : Fin 3) : Number :=
  foldSupport (List.ofFn points) (rotate base role) (dot (rotate base role) (points 0))

def total {n : ℕ} (points : Fin (n+1) → ExactPoint) (base : ExactPoint) : Number :=
  add (add (support points base 0) (support points base 1)) (support points base 2)

theorem support_le {n : ℕ} (points : Fin (n+1) → ExactPoint) (base : ExactPoint)
    (role : Fin 3) (bound : ℝ)
    (h : ∀ j, real (dot (rotate base role) (points j)) ≤ bound) :
    real (support points base role) ≤ bound := by
  apply foldSupport_le _ _ _ bound (h 0)
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

theorem total_le {n : ℕ} (points : Fin (n+1) → ExactPoint) (base : ExactPoint)
    (bounds : Fin 3 → ℝ)
    (h : ∀ i j, real (dot (rotate base i) (points j)) ≤ bounds i) :
    real (total points base) ≤ bounds 0 + bounds 1 + bounds 2 := by
  simp only [total, real_add]
  exact add_le_add (add_le_add (support_le _ _ _ _ (h 0))
    (support_le _ _ _ _ (h 1))) (support_le _ _ _ _ (h 2))

def eventCheck {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool) : Bool :=
  let s := total points (eventBase p q role negative)
  positive s && positive (sub (mul (ofRat 4) (square s))
    (mul (ofRat 3) (squaredDistance p q)))

theorem eventCheck_sound {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool)
    (accepted : eventCheck points p q role negative = true) :
    NICertificate.halfRoot * dist (toPlane p) (toPlane q) <
      real (total points (eventBase p q role negative)) := by
  obtain ⟨hpos, hgap⟩ := Bool.and_eq_true_iff.mp accepted
  have hs := positive_sound _ hpos
  have hg := positive_sound _ hgap
  simp only [real_sub, real_mul, real_ofRat, real_square, squaredDistance_real] at hg
  norm_num only [Rat.cast_ofNat] at hg
  have hh : NICertificate.halfRoot ^ 2 = (3/4 : ℝ) := by
    norm_num [NICertificate.halfRoot, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hh0 : 0 ≤ NICertificate.halfRoot := by unfold NICertificate.halfRoot; positivity
  have hd := dist_nonneg (x := toPlane p) (y := toPlane q)
  have hsq := sq_nonneg (real (total points (eventBase p q role negative)) -
    NICertificate.halfRoot * dist (toPlane p) (toPlane q))
  nlinarith [sq_nonneg (NICertificate.halfRoot * dist (toPlane p) (toPlane q)),
    congrArg (fun x : ℝ => x * dist (toPlane p) (toPlane q)^2) hh,
    mul_nonneg hh0 hd]

/-- Duplicate exact points are skipped. A separate positive-distance witness
ensures the source list really contains at least two distinct actual points. -/
def check {n : ℕ} (points : Fin (n+1) → ExactPoint) : Bool :=
  decide (∃ i j, positive (squaredDistance (points i) (points j)) = true) &&
  decide (∀ i j, points i ≠ points j →
    ∀ role : Fin 3, ∀ negative : Bool, eventCheck points (points i) (points j) role negative = true)


theorem check_distinct {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (accepted : check points = true) :
    ∃ i j, toPlane (points i) ≠ toPlane (points j) := by
  obtain ⟨hd, _⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨i, j, hij⟩ := of_decide_eq_true hd
  refine ⟨i, j, ?_⟩
  intro he
  have hs := positive_sound _ hij
  rw [squaredDistance_real, he, dist_self] at hs
  norm_num at hs

theorem check_event {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (accepted : check points = true) (i j : Fin (n+1))
    (hij : toPlane (points i) ≠ toPlane (points j))
    (role : Fin 3) (negative : Bool) :
    eventCheck points (points i) (points j) role negative = true := by
  have hevents := of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2
  exact hevents i j (fun h => hij (congrArg toPlane h)) role negative

end HexagonCover.ExactSupport
