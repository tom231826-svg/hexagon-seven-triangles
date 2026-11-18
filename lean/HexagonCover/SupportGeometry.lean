import HexagonCover.TriangleFrame
import HexagonCover.SupportEvents

/-!
# Geometric completeness of support events

The finite index used for the minimum argument must distinguish actual points.
Using the finite range of an original point list provides this without assuming
that the original list has no duplicates. The eventual event representatives
come from pairs of distinct actual points, rather than an externally parsed hull.
-/

namespace HexagonCover.SupportGeometry

noncomputable section

open TriangleFrame

/-- The three outward unit-normal directions associated with a base direction. -/
def nvec (c d : ℝ) (i : Fin 3) : Plane :=
  point (NICertificate.normalValues c d i).1 (NICertificate.normalValues c d i).2

theorem nvec_gram {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) (i j : Fin 3) :
    dotp (nvec c d i) (nvec c d j) = if i = j then 1 else -1 / 2 := by
  simpa only [nvec, dotp, point_coord_zero, point_coord_one, NICertificate.dot] using
    ExtremeTriangle.normal_dot hu i j

theorem dot_nvec_sum (c d : ℝ) (p : Plane) :
    ∑ i : Fin 3, dotp (nvec c d i) p = 0 := by
  simp [Fin.sum_univ_three, nvec, dotp, NICertificate.normalValues]
  ring

theorem nvec_smul (r c d : ℝ) (i : Fin 3) :
    nvec (r * c) (r * d) i = r • nvec c d i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [nvec, NICertificate.normalValues] <;> ring

theorem dot_nvec_linear (c d : ℝ) (i : Fin 3) (p : Plane) :
    dotp (nvec c d i) p = c * dotp (nvec 1 0 i) p + d * dotp (nvec 0 1 i) p := by
  fin_cases i <;> simp [nvec, dotp, NICertificate.normalValues] <;> ring

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def support (points : ι → Plane) (c d : ℝ) (i : Fin 3) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => dotp (nvec c d i) (points j))

def total (points : ι → Plane) (c d : ℝ) : ℝ := ∑ i : Fin 3, support points c d i

theorem dot_le_support (points : ι → Plane) (c d : ℝ) (i : Fin 3) (j : ι) :
    dotp (nvec c d i) (points j) ≤ support points c d i :=
  Finset.le_sup' (fun k => dotp (nvec c d i) (points k)) (Finset.mem_univ j)

theorem support_attained (points : ι → Plane) (c d : ℝ) (i : Fin 3) :
    ∃ j, support points c d i = dotp (nvec c d i) (points j) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j => dotp (nvec c d i) (points j))
  exact ⟨j, hj⟩

theorem support_smul (points : ι → Plane) {r : ℝ} (hr : 0 ≤ r) (c d : ℝ) (i : Fin 3) :
    support points (r * c) (r * d) i = r * support points c d i := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [nvec_smul, dotp_smul_left]
    exact mul_le_mul_of_nonneg_left (dot_le_support points c d i j) hr
  · obtain ⟨j, hj⟩ := support_attained points c d i
    rw [hj]
    simpa only [nvec_smul, dotp_smul_left] using
      dot_le_support points (r * c) (r * d) i j

theorem total_smul (points : ι → Plane) {r : ℝ} (hr : 0 ≤ r) (c d : ℝ) :
    total points (r * c) (r * d) = r * total points c d := by
  simp only [total, support_smul points hr, Finset.mul_sum]

/-- A nontrivial point set has strictly positive three-direction support sum. -/
theorem total_pos (points : ι → Plane) {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1)
    {a b : ι} (hne : points a ≠ points b) : 0 < total points c d := by
  by_contra hn
  have ht : total points c d ≤ 0 := le_of_not_gt hn
  simp only [total, Fin.sum_univ_three] at ht
  have heq (j : ι) : ∀ i, dotp (nvec c d i) (points j) = support points c d i := by
    have h0 := dot_le_support points c d 0 j
    have h1 := dot_le_support points c d 1 j
    have h2 := dot_le_support points c d 2 j
    have hs := dot_nvec_sum c d (points j)
    rw [Fin.sum_univ_three] at hs
    intro i
    fin_cases i
    · change dotp (nvec c d 0) (points j) = support points c d 0
      linarith
    · change dotp (nvec c d 1) (points j) = support points c d 1
      linarith
    · change dotp (nvec c d 2) (points j) = support points c d 2
      linarith
  apply hne
  exact eq_of_two_dot_eq (by simpa using nvec_gram hu 0 0)
    (by simpa using nvec_gram hu 1 1) (by simpa using nvec_gram hu 0 1)
    ((heq a 0).trans (heq b 0).symm) ((heq a 1).trans (heq b 1).symm)

/-- One branch chooses a support point separately for each of the three normals. -/
def branch (points : ι → Plane) (f : Fin 3 → ι) (c d : ℝ) : ℝ :=
  ∑ i : Fin 3, dotp (nvec c d i) (points (f i))

def branchA (points : ι → Plane) (f : Fin 3 → ι) : ℝ := branch points f 1 0
def branchB (points : ι → Plane) (f : Fin 3 → ι) : ℝ := branch points f 0 1

omit [Fintype ι] [Nonempty ι] in
theorem branch_linear (points : ι → Plane) (f : Fin 3 → ι) (c d : ℝ) :
    branch points f c d = c * branchA points f + d * branchB points f := by
  simp only [branchA, branchB, branch, Fin.sum_univ_three]
  rw [dot_nvec_linear c d 0, dot_nvec_linear c d 1, dot_nvec_linear c d 2]
  ring

theorem branch_le_total (points : ι → Plane) (f : Fin 3 → ι) (c d : ℝ) :
    branch points f c d ≤ total points c d := by
  apply Finset.sum_le_sum
  intro i _
  exact dot_le_support points c d i (f i)

theorem total_attained (points : ι → Plane) (c d : ℝ) :
    ∃ f : Fin 3 → ι, branch points f c d = total points c d := by
  classical
  choose f hf using support_attained points c d
  refine ⟨f, ?_⟩
  simp only [branch, total, hf]

omit [Fintype ι] [Nonempty ι] in
theorem trig_branch (points : ι → Plane) (f : Fin 3 → ι) (θ : ℝ) :
    SupportEvents.trigLinear (branchA points f) (branchB points f) θ =
      branch points f (Real.cos θ) (Real.sin θ) := by
  rw [branch_linear]
  unfold SupportEvents.trigLinear
  ring

/-- The sum of three finite supports is exactly the finite envelope of linear
trigonometric branches indexed by triples of actual points. -/
theorem envelope_eq_total (points : ι → Plane) (θ : ℝ) :
    SupportEvents.envelope
      (fun f : Fin 3 → ι => SupportEvents.trigLinear (branchA points f) (branchB points f)) θ =
      total points (Real.cos θ) (Real.sin θ) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro f _
    change SupportEvents.trigLinear (branchA points f) (branchB points f) θ ≤ _
    rw [trig_branch]
    exact branch_le_total points f _ _
  · obtain ⟨f, hf⟩ := total_attained points (Real.cos θ) (Real.sin θ)
    rw [← hf, ← trig_branch]
    exact SupportEvents.le_envelope
      (fun f : Fin 3 → ι => SupportEvents.trigLinear (branchA points f) (branchB points f)) f θ

/-- An active triple attains every one of its three individual supports. -/
theorem active_component (points : ι → Plane) (f : Fin 3 → ι) (c d : ℝ)
    (hactive : branch points f c d = total points c d) (i : Fin 3) :
    dotp (nvec c d i) (points (f i)) = support points c d i := by
  have h0 := dot_le_support points c d 0 (f 0)
  have h1 := dot_le_support points c d 1 (f 1)
  have h2 := dot_le_support points c d 2 (f 2)
  simp only [branch, total, Fin.sum_univ_three] at hactive
  fin_cases i
  · change dotp (nvec c d 0) (points (f 0)) = support points c d 0
    linarith
  · change dotp (nvec c d 1) (points (f 1)) = support points c d 1
    linarith
  · change dotp (nvec c d 2) (points (f 2)) = support points c d 2
    linarith

/-- The global minimum occurs at a normal supporting two distinct actual points.
Injectivity is supplied by indexing the finite set of actual points, rather
than by assuming that a source list contains no duplicates. -/
theorem minimum_at_support_pair (points : ι → Plane) (hinj : Function.Injective points)
    {a b : ι} (hab : a ≠ b) :
    ∃ θ : ℝ, ∃ i : Fin 3, ∃ j k : ι,
      points j ≠ points k ∧
      dotp (nvec (Real.cos θ) (Real.sin θ) i) (points j) =
        support points (Real.cos θ) (Real.sin θ) i ∧
      dotp (nvec (Real.cos θ) (Real.sin θ) i) (points k) =
        support points (Real.cos θ) (Real.sin θ) i ∧
      ∀ φ : ℝ, total points (Real.cos θ) (Real.sin θ) ≤
        total points (Real.cos φ) (Real.sin φ) := by
  have hpos (θ : ℝ) : 0 < SupportEvents.envelope
      (fun f : Fin 3 → ι => SupportEvents.trigLinear (branchA points f) (branchB points f)) θ := by
    rw [envelope_eq_total]
    exact total_pos points (Real.cos_sq_add_sin_sq θ) (hinj.ne hab)
  obtain ⟨θ, f, g, hfg, hf, hg, hmin⟩ :=
    SupportEvents.trig_envelope_minimum_at_tie (branchA points) (branchB points) hpos
  have hfa : branch points f (Real.cos θ) (Real.sin θ) = total points (Real.cos θ) (Real.sin θ) := by
    simpa only [trig_branch, envelope_eq_total] using hf
  have hga : branch points g (Real.cos θ) (Real.sin θ) = total points (Real.cos θ) (Real.sin θ) := by
    simpa only [trig_branch, envelope_eq_total] using hg
  have hdiff : ∃ i, f i ≠ g i := by
    by_contra h
    push Not at h
    exact hfg (funext h)
  obtain ⟨i, hi⟩ := hdiff
  refine ⟨θ, i, f i, g i, hinj.ne hi, active_component points f _ _ hfa i,
    active_component points g _ _ hga i, ?_⟩
  intro φ
  simpa only [envelope_eq_total] using hmin φ

def perpendicular (p : Plane) : Plane := point (-p 1) (p 0)
def signedPerpendicular (negative : Bool) (p : Plane) : Plane :=
  if negative then -perpendicular p else perpendicular p

def inverseRole : Fin 3 → Fin 3 := ![0, 2, 1]

/-- Six raw event directions per unordered pair: three normal roles and two
perpendicular signs. No normalization, hull parser, or floating point is used
in these real semantics. -/
def eventBase (p q : Plane) (i : Fin 3) (negative : Bool) : Plane :=
  let w := signedPerpendicular negative (q - p)
  nvec (w 0) (w 1) (inverseRole i)

theorem inverse_nvec (c d : ℝ) (i : Fin 3) :
    nvec ((nvec c d i) 0) ((nvec c d i) 1) (inverseRole i) = point c d := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [nvec, inverseRole, NICertificate.normalValues]
  all_goals nlinarith [congrArg (fun x : ℝ => x * c) ExtremeTriangle.halfRoot_sq,
    congrArg (fun x : ℝ => x * d) ExtremeTriangle.halfRoot_sq]

private theorem norm_sq_coordinates (p : Plane) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- There are exactly two unit normals perpendicular to a nonzero planar vector. -/
theorem perpendicular_unit_classification {δ n : Plane} (hδ : δ ≠ 0)
    (hunit : dotp n n = 1) (horth : dotp n δ = 0) :
    ∃ negative : Bool, n = ‖δ‖⁻¹ • signedPerpendicular negative δ := by
  let r := ‖δ‖
  let K := dotp n (perpendicular δ)
  have hr : 0 < r := norm_pos_iff.mpr hδ
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsq : r ^ 2 = δ 0 ^ 2 + δ 1 ^ 2 := norm_sq_coordinates δ
  have hK : K ^ 2 = r ^ 2 := by
    calc
      K ^ 2 = dotp n n * (δ 0 ^ 2 + δ 1 ^ 2) - dotp n δ ^ 2 := by
        unfold K dotp perpendicular
        simp only [point_coord_zero, point_coord_one]
        ring
      _ = r ^ 2 := by rw [hunit, horth]; nlinarith
  have hx : r ^ 2 * n 0 = -(δ 1) * K := by
    calc
      r ^ 2 * n 0 = (δ 0 ^ 2 + δ 1 ^ 2) * n 0 := by rw [hsq]
      _ = δ 0 * dotp n δ - δ 1 * K := by
        unfold K dotp perpendicular
        simp only [point_coord_zero, point_coord_one]
        ring
      _ = -(δ 1) * K := by rw [horth]; ring
  have hy : r ^ 2 * n 1 = δ 0 * K := by
    calc
      r ^ 2 * n 1 = (δ 0 ^ 2 + δ 1 ^ 2) * n 1 := by rw [hsq]
      _ = δ 1 * dotp n δ + δ 0 * K := by
        unfold K dotp perpendicular
        simp only [point_coord_zero, point_coord_one]
        ring
      _ = δ 0 * K := by rw [horth]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hK with hK | hK
  · have hx' : r * n 0 = -δ 1 := by
      have hh : r * (r * n 0 + δ 1) = 0 := by rw [hK] at hx; nlinarith
      have := (mul_eq_zero.mp hh).resolve_left hrne
      linarith
    have hy' : r * n 1 = δ 0 := by
      have hh : r * (r * n 1 - δ 0) = 0 := by rw [hK] at hy; nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hrne)
    have he : r • n = signedPerpendicular false δ := by
      ext i
      fin_cases i
      · exact hx'
      · exact hy'
    refine ⟨false, ?_⟩
    have := congrArg (fun p : Plane => r⁻¹ • p) he
    simpa only [smul_smul, inv_mul_cancel₀ hrne, one_smul] using this
  · have hx' : r * n 0 = δ 1 := by
      have hh : r * (r * n 0 - δ 1) = 0 := by rw [hK] at hx; nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hrne)
    have hy' : r * n 1 = -δ 0 := by
      have hh : r * (r * n 1 + δ 0) = 0 := by rw [hK] at hy; nlinarith
      have := (mul_eq_zero.mp hh).resolve_left hrne
      linarith
    have he : r • n = signedPerpendicular true δ := by
      ext i
      fin_cases i
      · simpa [signedPerpendicular, perpendicular] using hx'
      · exact hy'
    refine ⟨true, ?_⟩
    have := congrArg (fun p : Plane => r⁻¹ • p) he
    simpa only [smul_smul, inv_mul_cancel₀ hrne, one_smul] using this

/-- A tied support pair forces the base normal to one of the six normalized
representatives derived from that pair. -/
theorem normalized_event {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1)
    {p q : Plane} (hpq : p ≠ q) (i : Fin 3)
    (htie : dotp (nvec c d i) p = dotp (nvec c d i) q) :
    ∃ negative : Bool, point c d = ‖q - p‖⁻¹ • eventBase p q i negative := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hn : dotp (nvec c d i) (nvec c d i) = 1 := by simpa using nvec_gram hu i i
  have ho : dotp (nvec c d i) (q - p) = 0 := by rw [dotp_sub_right, htie]; ring
  obtain ⟨negative, he⟩ := perpendicular_unit_classification hδ hn ho
  refine ⟨negative, ?_⟩
  have h := congrArg (fun n : Plane => nvec (n 0) (n 1) (inverseRole i)) he
  rw [inverse_nvec] at h
  simpa only [PiLp.smul_apply, smul_eq_mul, nvec_smul, eventBase] using h

theorem eventBase_swap (p q : Plane) (i : Fin 3) (negative : Bool) :
    eventBase q p i (!negative) = eventBase p q i negative := by
  cases negative <;> simp [eventBase, signedPerpendicular, perpendicular, nvec,
    NICertificate.normalValues]

theorem support_le_of_range_subset {κ : Type*} [Fintype κ] [Nonempty κ]
    (points : ι → Plane) (other : κ → Plane) (hr : Set.range points ⊆ Set.range other)
    (c d : ℝ) (i : Fin 3) : support points c d i ≤ support other c d i := by
  apply Finset.sup'_le
  intro j _
  obtain ⟨k, hk⟩ := hr (Set.mem_range_self j)
  rw [← hk]
  exact dot_le_support other c d i k

theorem support_eq_of_range_eq {κ : Type*} [Fintype κ] [Nonempty κ]
    (points : ι → Plane) (other : κ → Plane) (hr : Set.range points = Set.range other)
    (c d : ℝ) (i : Fin 3) : support points c d i = support other c d i :=
  le_antisymm (support_le_of_range_subset points other hr.subset c d i)
    (support_le_of_range_subset other points hr.symm.subset c d i)

theorem total_eq_of_range_eq {κ : Type*} [Fintype κ] [Nonempty κ]
    (points : ι → Plane) (other : κ → Plane) (hr : Set.range points = Set.range other)
    (c d : ℝ) : total points c d = total other c d := by
  simp only [total, support_eq_of_range_eq points other hr]

/-- Source indices may contain duplicates: reduction to the actual finite range
preserves every support and still produces a pair of distinct actual points. -/
theorem minimum_at_support_pair_of_distinct (points : ι → Plane)
    {a b : ι} (hab : points a ≠ points b) :
    ∃ θ : ℝ, ∃ i : Fin 3, ∃ j k : ι,
      points j ≠ points k ∧
      dotp (nvec (Real.cos θ) (Real.sin θ) i) (points j) =
        support points (Real.cos θ) (Real.sin θ) i ∧
      dotp (nvec (Real.cos θ) (Real.sin θ) i) (points k) =
        support points (Real.cos θ) (Real.sin θ) i ∧
      ∀ φ : ℝ, total points (Real.cos θ) (Real.sin θ) ≤
        total points (Real.cos φ) (Real.sin φ) := by
  classical
  let : Fintype (Set.range points) := (Set.finite_range points).fintype
  let : Nonempty (Set.range points) := ⟨⟨points a, Set.mem_range_self a⟩⟩
  let reduced : Set.range points → Plane := Subtype.val
  let ia : Set.range points := ⟨points a, Set.mem_range_self a⟩
  let ib : Set.range points := ⟨points b, Set.mem_range_self b⟩
  have hiab : ia ≠ ib := by
    intro heq
    exact hab (congrArg Subtype.val heq)
  have hrange : Set.range reduced = Set.range points := by
    ext p
    constructor
    · rintro ⟨j, rfl⟩
      exact j.property
    · intro hp
      exact ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨θ, i, j, k, hjk, hj, hk, hmin⟩ :=
    minimum_at_support_pair reduced Subtype.coe_injective hiab
  obtain ⟨j', hj'⟩ := j.property
  obtain ⟨k', hk'⟩ := k.property
  dsimp only [reduced] at hjk
  refine ⟨θ, i, j', k', ?_, ?_, ?_, ?_⟩
  · rw [hj', hk']
    exact hjk
  · rw [hj']
    exact hj.trans (support_eq_of_range_eq reduced points hrange _ _ i)
  · rw [hk']
    exact hk.trans (support_eq_of_range_eq reduced points hrange _ _ i)
  · intro φ
    simpa only [total_eq_of_range_eq reduced points hrange] using hmin φ

/-- Raw event support equals the unit support multiplied by the pair length. -/
theorem total_event_scale (points : ι → Plane) {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1)
    {p q : Plane} (hpq : p ≠ q) (i : Fin 3)
    (htie : dotp (nvec c d i) p = dotp (nvec c d i) q) :
    ∃ negative : Bool,
      total points ((eventBase p q i negative) 0) ((eventBase p q i negative) 1) =
        ‖q - p‖ * total points c d := by
  obtain ⟨negative, he⟩ := normalized_event hu hpq i htie
  have hr : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq.symm)
  have hscaled := congrArg (fun n : Plane => ‖q - p‖ • n) he
  have hraw : eventBase p q i negative = ‖q - p‖ • point c d := by
    simpa only [smul_smul, mul_inv_cancel₀ hr, one_smul] using hscaled.symm
  refine ⟨negative, ?_⟩
  rw [hraw]
  simp only [PiLp.smul_apply, smul_eq_mul, point_coord_zero, point_coord_one]
  exact total_smul points (norm_nonneg _) c d

/-- The six exact unnormalized event inequalities for every distinct point pair. -/
def EventBound (points : ι → Plane) (bound : ℝ) : Prop :=
  ∀ j k, points j ≠ points k → ∀ i : Fin 3, ∀ negative : Bool,
    bound * ‖points k - points j‖ <
      total points ((eventBase (points j) (points k) i negative) 0)
        ((eventBase (points j) (points k) i negative) 1)

/-- Finite pair events suffice for a uniform bound over every angle, including
all intermediate angles. No hull ordering or distinct source-index assumption
is present. -/
theorem bound_of_eventBounds (points : ι → Plane) {a b : ι}
    (hab : points a ≠ points b) {bound : ℝ} (hevents : EventBound points bound) :
    ∀ θ : ℝ, bound < total points (Real.cos θ) (Real.sin θ) := by
  obtain ⟨φ, i, j, k, hjk, hj, hk, hmin⟩ := minimum_at_support_pair_of_distinct points hab
  obtain ⟨negative, hscale⟩ := total_event_scale points (Real.cos_sq_add_sin_sq φ) hjk i
    (hj.trans hk.symm)
  have hb := hevents j k hjk i negative
  rw [hscale] at hb
  have hr : 0 < ‖points k - points j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hjk.symm)
  have hφ : bound < total points (Real.cos φ) (Real.sin φ) := by
    apply (mul_lt_mul_iff_of_pos_left hr).mp
    simpa only [mul_comm bound ‖points k - points j‖] using hb
  intro θ
  exact hφ.trans_le (hmin θ)

/-- The chart chosen for every actual triangle lies in this closed semicircle. -/
theorem bound_of_eventBounds_semicircle (points : ι → Plane) {a b : ι}
    (hab : points a ≠ points b) {bound : ℝ} (hevents : EventBound points bound)
    {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) (hc : 0 ≤ c) : bound < total points c d := by
  have hd0 : -1 ≤ d := by nlinarith [sq_nonneg c]
  have hd1 : d ≤ 1 := by nlinarith [sq_nonneg c]
  have hs := Real.sin_arcsin hd0 hd1
  have hcos : Real.cos (Real.arcsin d) = c := by
    have hunit := Real.cos_sq_add_sin_sq (Real.arcsin d)
    rw [hs] at hunit
    nlinarith [Real.cos_arcsin_nonneg d]
  have h := bound_of_eventBounds points hab hevents (Real.arcsin d)
  rwa [hs, hcos] at h

/-- A successful complete support-event bound excludes an actual arbitrary
closed unit triangle containing every original source point. -/
theorem cannot_contain_of_eventBounds (points : ι → Plane) {a b : ι}
    (hab : points a ≠ points b) (hevents : EventBound points NICertificate.halfRoot)
    (T : UnitTriangle) (hcontained : ∀ j, points j ∈ T.region) : False := by
  obtain ⟨c, d, offsets, hc, hu, hsum, hmem⟩ := TriangleFrame.exists_normal_frame T
  have hs (i : Fin 3) : support points c d i ≤ offsets i := by
    apply Finset.sup'_le
    intro j _
    change NICertificate.dot (NICertificate.normalValues c d i) ((points j) 0, (points j) 1) ≤ offsets i
    exact (hmem (points j)).mp (hcontained j) i
  have hupper : total points c d ≤ NICertificate.halfRoot := by
    simp only [total, Fin.sum_univ_three]
    linarith [hs 0, hs 1, hs 2]
  exact (not_lt_of_ge hupper) (bound_of_eventBounds_semicircle points hab hevents hu hc)

end
end HexagonCover.SupportGeometry
