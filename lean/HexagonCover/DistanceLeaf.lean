import HexagonCover.Quadratic3
import HexagonCover.Geometry

/-!+# Exact diameter leaves

The executable leaf predicate uses rational-pair arithmetic. The soundness
theorem interprets its points in the actual Euclidean plane and applies the
diameter bound for the entire closed unit equilateral triangle.

The final example is one explicit pair from the frozen original Q25 fact journal.
It proves that pair cannot belong to one unit triangle. The source identifiers
are provenance data, not a proof that all original tree paths have been loaded.
-/

namespace HexagonCover.DistanceLeaf

open Quadratic3

structure ExactPoint where
  x : Number
  y : Number
  deriving DecidableEq, Repr

/-- The original triple `(x,b,c)` denotes Cartesian `(x,b+c√3)`. -/
def fromXYZ (x b c : ℚ) : ExactPoint := ⟨ofRat x, (b, c)⟩

noncomputable def toPlane (p : ExactPoint) : Plane := point (real p.x) (real p.y)

def squaredDistance (p q : ExactPoint) : Number :=
  add (square (sub p.x q.x)) (square (sub p.y q.y))

theorem squaredDistance_real (p q : ExactPoint) :
    real (squaredDistance p q) = dist (toPlane p) (toPlane q) ^ 2 := by
  simp only [squaredDistance, real_add, real_square, real_sub, toPlane, dist_point_sq]

/-- Strict excess over the squared unit diameter. Tangency at distance one
does not yield a successful leaf. -/
def check (p q : ExactPoint) : Bool :=
  positive (sub (squaredDistance p q) (ofRat 1))

theorem check_sound {p q : ExactPoint} (accepted : check p q = true) :
    1 < dist (toPlane p) (toPlane q) := by
  have h := positive_sound _ accepted
  rw [real_sub, real_ofRat, squaredDistance_real] at h
  norm_num only [Rat.cast_one] at h
  have hn : 0 ≤ dist (toPlane p) (toPlane q) := dist_nonneg
  nlinarith

/-- The checker excludes simultaneous membership in an actual closed unit
triangle, with no assumptions on its translation or rotation. -/
theorem cannot_belong_to_unitTriangle {p q : ExactPoint}
    (accepted : check p q = true) (T : UnitTriangle) :
    ¬ (toPlane p ∈ T.region ∧ toPlane q ∈ T.region) := by
  rintro ⟨hp, hq⟩
  exact (not_lt_of_ge (T.dist_le_one hp hq)) (check_sound accepted)

/-- A source witness names two positions in the actual obligation list.
Out-of-range positions fail instead of supplying default coordinates. -/
def checkWitness (points : List ExactPoint) (positions : Nat × Nat) : Bool :=
  match points[positions.1]?, points[positions.2]? with
  | some p, some q => check p q
  | _, _ => false

/-- The list-level form needed by an owner-tree leaf checker. -/
theorem checkWitness_sound {points : List ExactPoint} {positions : Nat × Nat}
    (accepted : checkWitness points positions = true) (T : UnitTriangle)
    (contained : ∀ p, p ∈ points → toPlane p ∈ T.region) : False := by
  cases hp : points[positions.1]? with
  | none => simp [checkWitness, hp] at accepted
  | some p =>
      cases hq : points[positions.2]? with
      | none => simp [checkWitness, hp, hq] at accepted
      | some q =>
          have hcheck : check p q = true := by
            simpa [checkWitness, hp, hq] using accepted
          exact cannot_belong_to_unitTriangle hcheck T
            ⟨contained p (List.mem_of_getElem? hp), contained q (List.mem_of_getElem? hq)⟩

/-- Byte identities and file-local indices for the explicit real example.
These fields are not used as trusted mathematical premises. -/
structure SourceBinding where
  family : String
  factId : Nat
  role : Fin 7
  anchorId : Nat
  pointIds : List Nat
  pointTriples : List (ℚ × ℚ × ℚ)
  witnessPositions : Nat × Nat
  originalFlag : Bool
  nonintrudingRole : Bool
  compressedTreeSHA256 : String
  obligationIdentity : String
  journalRelativePath : String
  journalSHA256 : String
  journalLine : Nat
  deriving Repr

def q25Fact0Binding : SourceBinding where
  family := "Q25"
  factId := 0
  role := 0
  anchorId := 253
  pointIds := [253, 0]
  pointTriples := [(1, 0, 0), (-1, 0, 0)]
  witnessPositions := (0, 1)
  originalFlag := false
  nonintrudingRole := false
  compressedTreeSHA256 := "4b8f1ccf9192e3afb2052473a9d5111b632648a33fb29483aabc7346137688b9"
  obligationIdentity := "bc1f8eec2ed31785ea509b604670ac834cb49264afa0728e48f4ca66fa8e6e82"
  journalRelativePath := "work/research_control/state/runs/ee5cb6ec53ef4feba040a8dbff3e4a26/verdict-facts/Q25.jsonl"
  journalSHA256 := "ea78462b7ac22e7e11b3fde5006d8a40068234919c129943bb926b9f6a2efe17"
  journalLine := 1

def q25Fact0Anchor : ExactPoint := fromXYZ 1 0 0
def q25Fact0Witness : ExactPoint := fromXYZ (-1) 0 0

/-- Kernel reduction checks the actual explicit rational pair. -/
theorem q25Fact0_check : check q25Fact0Anchor q25Fact0Witness = true := by
  decide +kernel

/-- The recorded pair positions are checked against the explicit obligation list. -/
theorem q25Fact0_witness_check :
    checkWitness [q25Fact0Anchor, q25Fact0Witness] q25Fact0Binding.witnessPositions = true := by
  decide +kernel

/-- One actual source-bound diameter leaf, without claiming whole-tree closure. -/
theorem q25Fact0_excluded (T : UnitTriangle) :
    ¬ (toPlane q25Fact0Anchor ∈ T.region ∧ toPlane q25Fact0Witness ∈ T.region) :=
  cannot_belong_to_unitTriangle q25Fact0_check T

end HexagonCover.DistanceLeaf
