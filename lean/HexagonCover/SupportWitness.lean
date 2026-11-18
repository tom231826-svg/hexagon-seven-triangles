import HexagonCover.SupportConsumer

/-! A support event can be certified by any three selected source points,
one for each normal. Their sum is a lower bound on the true support total.
Selection indices are actual `Fin` values: out-of-range data cannot wrap.
Individual event proofs can be combined without recomputing a monolithic
finite universal decision. No maximum or old support assertion is trusted. -/
namespace HexagonCover.SupportWitness
open DistanceLeaf Quadratic3

abbrev Selection (n : ℕ) := Fin 3 → Fin (n+1)
abbrev Selections (n : ℕ) :=
  Fin (n+1) → Fin (n+1) → Fin 3 → Bool → Selection n

def eventSum {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool)
    (selected : Selection n) : Number :=
  let base := ExactSupport.eventBase p q role negative
  add (add (ExactSupport.dot (ExactSupport.rotate base 0) (points (selected 0)))
    (ExactSupport.dot (ExactSupport.rotate base 1) (points (selected 1))))
    (ExactSupport.dot (ExactSupport.rotate base 2) (points (selected 2)))

def eventCheck {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool)
    (selected : Selection n) : Bool :=
  let s := eventSum points p q role negative selected
  positive s && positive (sub (mul (ofRat 4) (square s))
    (mul (ofRat 3) (squaredDistance p q)))

theorem eventCheck_sound {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool)
    (selected : Selection n)
    (accepted : eventCheck points p q role negative selected = true) :
    NICertificate.halfRoot * dist (toPlane p) (toPlane q) <
      real (eventSum points p q role negative selected) := by
  obtain ⟨hpos, hgap⟩ := Bool.and_eq_true_iff.mp accepted
  have hs := positive_sound _ hpos
  have hg := positive_sound _ hgap
  simp only [real_sub, real_mul, real_ofRat, real_square, squaredDistance_real] at hg
  norm_num only [Rat.cast_ofNat] at hg
  have hh : NICertificate.halfRoot ^ 2 = (3/4 : ℝ) := by
    norm_num [NICertificate.halfRoot, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hh0 : 0 ≤ NICertificate.halfRoot := by unfold NICertificate.halfRoot; positivity
  have hd := dist_nonneg (x := toPlane p) (y := toPlane q)
  have hsq := sq_nonneg (real (eventSum points p q role negative selected) -
    NICertificate.halfRoot * dist (toPlane p) (toPlane q))
  nlinarith [sq_nonneg (NICertificate.halfRoot * dist (toPlane p) (toPlane q)),
    congrArg (fun x : ℝ => x * dist (toPlane p) (toPlane q)^2) hh,
    mul_nonneg hh0 hd]

theorem eventSum_le_geometric {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool)
    (selected : Selection n) :
    real (eventSum points p q role negative selected) ≤
      SupportGeometry.total (fun j => toPlane (points j))
        (toPlane (ExactSupport.eventBase p q role negative) 0)
        (toPlane (ExactSupport.eventBase p q role negative) 1) := by
  unfold eventSum SupportGeometry.total
  simp only [real_add, Fin.sum_univ_three]
  apply add_le_add
  · apply add_le_add
    · rw [SupportConsumer.dot_rotate_real]
      exact SupportGeometry.dot_le_support (fun j : Fin (n+1) => toPlane (points j))
        (toPlane (ExactSupport.eventBase p q role negative) 0)
        (toPlane (ExactSupport.eventBase p q role negative) 1) 0 (selected 0)
    · rw [SupportConsumer.dot_rotate_real]
      exact SupportGeometry.dot_le_support (fun j : Fin (n+1) => toPlane (points j))
        (toPlane (ExactSupport.eventBase p q role negative) 0)
        (toPlane (ExactSupport.eventBase p q role negative) 1) 1 (selected 1)
  · rw [SupportConsumer.dot_rotate_real]
    exact SupportGeometry.dot_le_support (fun j : Fin (n+1) => toPlane (points j))
      (toPlane (ExactSupport.eventBase p q role negative) 0)
      (toPlane (ExactSupport.eventBase p q role negative) 1) 2 (selected 2)

structure Checked {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : Selections n) : Prop where
  distinct : ∃ i j, positive (squaredDistance (points i) (points j)) = true
  events : ∀ i j, points i ≠ points j → ∀ role negative,
    eventCheck points (points i) (points j) role negative (selected i j role negative) = true

def check {n : ℕ} (points : Fin (n+1) → ExactPoint) (selected : Selections n) : Bool :=
  decide (∃ i j, positive (squaredDistance (points i) (points j)) = true) &&
  decide (∀ i j, points i ≠ points j → ∀ role negative,
    eventCheck points (points i) (points j) role negative (selected i j role negative) = true)

theorem checked_of_check {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : Selections n) (accepted : check points selected = true) :
    Checked points selected := by
  obtain ⟨hd, he⟩ := Bool.and_eq_true_iff.mp accepted
  exact ⟨of_decide_eq_true hd, of_decide_eq_true he⟩

theorem check_of_checked {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : Selections n) (accepted : Checked points selected) :
    check points selected = true := by
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true accepted.distinct,
    decide_eq_true accepted.events⟩

theorem checked_sound {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : Selections n) (accepted : Checked points selected) (T : UnitTriangle)
    (contained : ∀ j, toPlane (points j) ∈ T.region) : False := by
  obtain ⟨a, b, hab⟩ := accepted.distinct
  have hab' : toPlane (points a) ≠ toPlane (points b) := by
    intro he
    have hs := positive_sound _ hab
    rw [squaredDistance_real, he, dist_self] at hs
    norm_num at hs
  apply SupportGeometry.cannot_contain_of_eventBounds (fun j => toPlane (points j)) hab' ?_ T contained
  intro j k hjk role negative
  have hne : points j ≠ points k := fun h => hjk (congrArg toPlane h)
  have h := eventCheck_sound points (points j) (points k) role negative
    (selected j k role negative) (accepted.events j k hne role negative)
  have hg := eventSum_le_geometric points (points j) (points k) role negative
    (selected j k role negative)
  rw [SupportConsumer.eventBase_real] at hg
  have hfinal := h.trans_le hg
  simpa only [dist_eq_norm, norm_sub_rev] using hfinal

theorem check_sound {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : Selections n) (accepted : check points selected = true) (T : UnitTriangle)
    (contained : ∀ j, toPlane (points j) ∈ T.region) : False :=
  checked_sound points selected (checked_of_check points selected accepted) T contained

structure Certificate where
  sizePred : ℕ
  points : Fin (sizePred+1) → ExactPoint
  selected : Selections sizePred

structure CheckedCertificate where
  certificate : Certificate
  checked : Checked certificate.points certificate.selected

def membershipCheck (obligations : List ExactPoint) (certificate : Certificate) : Bool :=
  decide (∀ i, certificate.points i ∈ obligations)

theorem CheckedCertificate.excluded (c : CheckedCertificate) (obligations : List ExactPoint)
    (member : membershipCheck obligations c.certificate = true) (T : UnitTriangle)
    (contained : ∀ p ∈ obligations, toPlane p ∈ T.region) : False := by
  have hm := of_decide_eq_true member
  exact checked_sound c.certificate.points c.certificate.selected c.checked T
    (fun i => contained (c.certificate.points i) (hm i))

end HexagonCover.SupportWitness
