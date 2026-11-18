import HexagonCover.SupportWitnessSymmetry

/-! Homogeneous integer Q(√3) arithmetic for the same selected-support event.
The positive denominator is shared by all source coordinates. Integer checks
are transported to the existing rational event checker by exact identities;
neither a numerical approximation nor a stored verdict is a proof premise. -/
namespace HexagonCover.SupportInteger
open DistanceLeaf

abbrev ZNumber := ℤ × ℤ
def zadd (a b : ZNumber) : ZNumber := (a.1+b.1, a.2+b.2)
def zneg (a : ZNumber) : ZNumber := (-a.1, -a.2)
def zsub (a b : ZNumber) : ZNumber := zadd a (zneg b)
def zmul (a b : ZNumber) : ZNumber := (a.1*b.1+3*a.2*b.2, a.1*b.2+a.2*b.1)
def zsquare (a : ZNumber) : ZNumber := zmul a a
def zofInt (a : ℤ) : ZNumber := (a,0)
def zroot : ZNumber := (0,1)
def embed (a : ZNumber) : Quadratic3.Number := ((a.1 : ℚ), (a.2 : ℚ))
noncomputable def zreal (a : ZNumber) : ℝ := Quadratic3.real (embed a)

theorem embed_add (a b : ZNumber) : embed (zadd a b) = Quadratic3.add (embed a) (embed b) := by
  apply Prod.ext <;> simp [embed, zadd, Quadratic3.add]
theorem embed_neg (a : ZNumber) : embed (zneg a) = Quadratic3.neg (embed a) := by
  apply Prod.ext <;> simp [embed, zneg, Quadratic3.neg]
theorem embed_mul (a b : ZNumber) : embed (zmul a b) = Quadratic3.mul (embed a) (embed b) := by
  apply Prod.ext <;> simp [embed, zmul, Quadratic3.mul]

@[simp] theorem zreal_add (a b : ZNumber) : zreal (zadd a b) = zreal a + zreal b := by
  simp [zreal, embed_add]
@[simp] theorem zreal_neg (a : ZNumber) : zreal (zneg a) = -zreal a := by
  simp [zreal, embed_neg]
@[simp] theorem zreal_sub (a b : ZNumber) : zreal (zsub a b) = zreal a - zreal b := by
  simp [zsub, sub_eq_add_neg]
@[simp] theorem zreal_mul (a b : ZNumber) : zreal (zmul a b) = zreal a * zreal b := by
  simp [zreal, embed_mul]
@[simp] theorem zreal_square (a : ZNumber) : zreal (zsquare a) = zreal a ^ 2 := by
  simp [zsquare, pow_two]
@[simp] theorem zreal_ofInt (a : ℤ) : zreal (zofInt a) = (a : ℝ) := by
  simp [zreal, embed, zofInt, Quadratic3.real]
@[simp] theorem zreal_root : zreal zroot = Real.sqrt 3 := by
  norm_num [zreal, embed, zroot, Quadratic3.real]

def positive (a : ZNumber) : Bool := decide
  ((0 ≤ a.1 ∧ 0 ≤ a.2 ∧ (0 < a.1 ∨ 0 < a.2)) ∨
   (0 ≤ a.1 ∧ a.2 ≤ 0 ∧ 3*a.2^2 < a.1^2) ∨
   (a.1 ≤ 0 ∧ 0 ≤ a.2 ∧ a.1^2 < 3*a.2^2))

theorem positive_sound (a : ZNumber) (accepted : positive a = true) : 0 < zreal a := by
  have h := of_decide_eq_true accepted
  apply Quadratic3.positive_sound
  apply decide_eq_true
  change ((0 : ℚ) ≤ (a.1 : ℚ) ∧ 0 ≤ (a.2 : ℚ) ∧ (0 < (a.1 : ℚ) ∨ 0 < (a.2 : ℚ))) ∨
    (0 ≤ (a.1 : ℚ) ∧ (a.2 : ℚ) ≤ 0 ∧ 3*(a.2 : ℚ)^2 < (a.1 : ℚ)^2) ∨
    ((a.1 : ℚ) ≤ 0 ∧ 0 ≤ (a.2 : ℚ) ∧ (a.1 : ℚ)^2 < 3*(a.2 : ℚ)^2)
  exact_mod_cast h

structure Point where
  x : ZNumber
  y : ZNumber
  deriving DecidableEq, Repr

def decode (denominator : ℤ) (p : Point) : ExactPoint :=
  ⟨Quadratic3.mul (Quadratic3.ofRat (1/(denominator : ℚ))) (embed p.x),
   Quadratic3.mul (Quadratic3.ofRat (1/(denominator : ℚ))) (embed p.y)⟩

@[simp] theorem decode_x_real (d : ℤ) (p : Point) :
    Quadratic3.real (decode d p).x = zreal p.x / (d : ℝ) := by
  simp [decode, zreal, div_eq_mul_inv]
  ring
@[simp] theorem decode_y_real (d : ℤ) (p : Point) :
    Quadratic3.real (decode d p).y = zreal p.y / (d : ℝ) := by
  simp [decode, zreal, div_eq_mul_inv]
  ring

def negate (p : Point) : Point := ⟨zneg p.x, zneg p.y⟩
def difference (p q : Point) : Point := ⟨zsub p.x q.x, zsub p.y q.y⟩
def perpendicular (p : Point) : Point := ⟨zneg p.y, p.x⟩
def base (p q : Point) (negative : Bool) : Point :=
  let w := perpendicular (difference q p)
  if negative then negate w else w
def doubledNormals (p : Point) : Fin 3 → Point
  | 0 => ⟨zmul (zofInt 2) p.x, zmul (zofInt 2) p.y⟩
  | 1 => ⟨zsub (zneg p.x) (zmul zroot p.y), zsub (zmul zroot p.x) p.y⟩
  | 2 => ⟨zadd (zneg p.x) (zmul zroot p.y), zsub (zneg (zmul zroot p.x)) p.y⟩
def dot (p q : Point) : ZNumber := zadd (zmul p.x q.x) (zmul p.y q.y)
def distanceSquared (p q : Point) : ZNumber :=
  zadd (zsquare (zsub p.x q.x)) (zsquare (zsub p.y q.y))

theorem base_x_real (d : ℤ) (p q : Point) (negative : Bool) :
    Quadratic3.real (ExactSupport.eventBase (decode d p) (decode d q) 0 negative).x =
      zreal (base p q negative).x / (d : ℝ) := by
  cases negative <;>
    simp [ExactSupport.eventBase, ExactSupport.rotate, ExactSupport.inverseRole,
      ExactSupport.negate, ExactSupport.perpendicular, ExactSupport.difference,
      base, negate, perpendicular, difference, div_eq_mul_inv] <;> ring
theorem base_y_real (d : ℤ) (p q : Point) (negative : Bool) :
    Quadratic3.real (ExactSupport.eventBase (decode d p) (decode d q) 0 negative).y =
      zreal (base p q negative).y / (d : ℝ) := by
  cases negative <;>
    simp [ExactSupport.eventBase, ExactSupport.rotate, ExactSupport.inverseRole,
      ExactSupport.negate, ExactSupport.perpendicular, ExactSupport.difference,
      base, negate, perpendicular, difference, div_eq_mul_inv] <;> ring

theorem normal_x_real (d : ℤ) (p q : Point) (negative : Bool) (role : Fin 3) :
    Quadratic3.real (ExactSupport.rotate (ExactSupport.eventBase (decode d p) (decode d q) 0 negative) role).x =
      zreal (doubledNormals (base p q negative) role).x / (2*(d : ℝ)) := by
  fin_cases role <;>
    simp [ExactSupport.rotate, ExactSupport.real_halfRoot, NICertificate.halfRoot,
      base_x_real, base_y_real, doubledNormals, div_eq_mul_inv, mul_inv_rev] <;> ring
theorem normal_y_real (d : ℤ) (p q : Point) (negative : Bool) (role : Fin 3) :
    Quadratic3.real (ExactSupport.rotate (ExactSupport.eventBase (decode d p) (decode d q) 0 negative) role).y =
      zreal (doubledNormals (base p q negative) role).y / (2*(d : ℝ)) := by
  fin_cases role <;>
    simp [ExactSupport.rotate, ExactSupport.real_halfRoot, NICertificate.halfRoot,
      base_x_real, base_y_real, doubledNormals, div_eq_mul_inv, mul_inv_rev] <;> ring

def eventSum {n : ℕ} (points : Fin (n+1) → Point) (p q : Point)
    (negative : Bool) (selected : SupportWitness.Selection n) : ZNumber :=
  let normals := doubledNormals (base p q negative)
  zadd (zadd (dot (normals 0) (points (selected 0)))
    (dot (normals 1) (points (selected 1)))) (dot (normals 2) (points (selected 2)))

private theorem qdot_real (p q : ExactPoint) : Quadratic3.real (ExactSupport.dot p q) =
    Quadratic3.real p.x * Quadratic3.real q.x + Quadratic3.real p.y * Quadratic3.real q.y := by
  simp [ExactSupport.dot]

theorem eventSum_real {n : ℕ} (d : ℤ) (points : Fin (n+1) → Point) (p q : Point)
    (negative : Bool) (selected : SupportWitness.Selection n) :
    Quadratic3.real (SupportWitness.eventSum (fun i => decode d (points i))
      (decode d p) (decode d q) 0 negative selected) =
      zreal (eventSum points p q negative selected) / (2*(d : ℝ)^2) := by
  unfold SupportWitness.eventSum
  simp only [Quadratic3.real_add, qdot_real, normal_x_real, normal_y_real,
    decode_x_real, decode_y_real]
  simp [eventSum, dot, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem distanceSquared_real (d : ℤ) (p q : Point) :
    Quadratic3.real (squaredDistance (decode d p) (decode d q)) =
      zreal (distanceSquared p q) / (d : ℝ)^2 := by
  simp [squaredDistance, distanceSquared, div_eq_mul_inv, inv_pow]
  ring

def eventCheck {n : ℕ} (d : ℤ) (points : Fin (n+1) → Point) (p q : Point)
    (negative : Bool) (selected : SupportWitness.Selection n) : Bool :=
  let s := eventSum points p q negative selected
  positive s && positive (zsub (zsquare s) (zmul (zofInt (3*d^2)) (distanceSquared p q)))

theorem eventCheck_sound {n : ℕ} (d : ℤ) (hd : 0 < d)
    (points : Fin (n+1) → Point) (p q : Point) (negative : Bool)
    (selected : SupportWitness.Selection n)
    (accepted : eventCheck d points p q negative selected = true) :
    SupportWitness.eventCheck (fun i => decode d (points i))
      (decode d p) (decode d q) 0 negative selected = true := by
  obtain ⟨hs, hg⟩ := Bool.and_eq_true_iff.mp accepted
  have hs' := positive_sound _ hs
  have hg' := positive_sound _ hg
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hd'
  simp only [zreal_sub, zreal_square, zreal_mul, zreal_ofInt] at hg'
  push_cast at hg'
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Quadratic3.positive_complete
    rw [eventSum_real]
    exact div_pos hs' (by positivity)
  · apply Quadratic3.positive_complete
    simp only [Quadratic3.real_sub, Quadratic3.real_mul, Quadratic3.real_ofRat, Quadratic3.real_square]
    norm_num only [Rat.cast_ofNat]
    rw [eventSum_real, distanceSquared_real]
    have heq : 4*(zreal (eventSum points p q negative selected)/(2*(d : ℝ)^2))^2 -
        3*(zreal (distanceSquared p q)/(d : ℝ)^2) =
        (zreal (eventSum points p q negative selected)^2 -
          3*(d : ℝ)^2*zreal (distanceSquared p q))/(d : ℝ)^4 := by
      field_simp
      ring
    rw [heq]
    exact div_pos hg' (pow_pos hd' 4)

end HexagonCover.SupportInteger
