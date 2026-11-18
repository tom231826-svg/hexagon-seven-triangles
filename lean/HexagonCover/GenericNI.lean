import HexagonCover.TriangleFrame
import HexagonCover.DistanceLeaf

/-!
Reusable normalized-infeasibility interval consumer. Inputs are the exact
obligation list and a rational squared radius. This module reuses the proved
interval and scalar geometry primitives; it never trusts producer status flags.
-/

namespace HexagonCover.GenericNI

open NICertificate ExtremeTriangle DistanceLeaf

def numberRange (z : Quadratic3.Number) : Exact.Interval :=
  Exact.add (Exact.singleton z.1) (Exact.mul (Exact.singleton z.2) sqrt3Interval)

theorem numberRange_sound (z : Quadratic3.Number) :
    (numberRange z).Contains (Quadratic3.real z) :=
  Exact.add_contains (Exact.singleton_contains z.1)
    (Exact.mul_contains (Exact.singleton_contains z.2) sqrt3Interval_sound)

def pointRange (p : ExactPoint) : IVec := (numberRange p.x, numberRange p.y)
noncomputable def pointValue (p : ExactPoint) : RVec := (Quadratic3.real p.x, Quadratic3.real p.y)

theorem pointRange_sound (p : ExactPoint) : ContainsV (pointRange p) (pointValue p) :=
  ⟨numberRange_sound p.x, numberRange_sound p.y⟩

def supportTailRange (N : IVec) (I : Exact.Interval) : List ExactPoint → Exact.Interval
  | [] => I
  | p :: rest => supportTailRange N (maximum I (dotRange N (pointRange p))) rest

noncomputable def supportTailValue (n : RVec) (r : ℝ) : List ExactPoint → ℝ
  | [] => r
  | p :: rest => supportTailValue n (max r (dot n (pointValue p))) rest

theorem supportTailRange_sound {N : IVec} {n : RVec} (hn : ContainsV N n)
    (points : List ExactPoint) (I : Exact.Interval) (r : ℝ) (hr : I.Contains r) :
    (supportTailRange N I points).Contains (supportTailValue n r points) := by
  induction points generalizing I r with
  | nil => exact hr
  | cons p rest ih =>
      exact ih _ _ (maximum_sound hr (dotRange_sound hn (pointRange_sound p)))

def supportRange (points : List ExactPoint) (N : IVec) : Exact.Interval :=
  match points with
  | [] => Exact.singleton 0
  | p :: rest => supportTailRange N (dotRange N (pointRange p)) rest

noncomputable def supportValue (points : List ExactPoint) (n : RVec) : ℝ :=
  match points with
  | [] => 0
  | p :: rest => supportTailValue n (dot n (pointValue p)) rest

theorem supportRange_sound {N : IVec} {n : RVec} (hn : ContainsV N n) (points : List ExactPoint) :
    (supportRange points N).Contains (supportValue points n) := by
  cases points with
  | nil => simpa [supportRange, supportValue] using Exact.singleton_contains 0
  | cons p rest =>
      exact supportTailRange_sound hn rest _ _ (dotRange_sound hn (pointRange_sound p))

theorem supportTailValue_upper (n : RVec) (b : ℝ) (points : List ExactPoint)
    (r : ℝ) (hr : r ≤ b) (hp : ∀ p ∈ points, dot n (pointValue p) ≤ b) :
    supportTailValue n r points ≤ b := by
  induction points generalizing r with
  | nil => exact hr
  | cons p rest ih =>
      apply ih _ (max_le hr (hp p (by simp)))
      intro q hq
      exact hp q (by simp [hq])

theorem supportValue_upper (points : List ExactPoint) (hne : points ≠ []) (n : RVec) (b : ℝ)
    (hp : ∀ p ∈ points, dot n (pointValue p) ≤ b) : supportValue points n ≤ b := by
  cases points with
  | nil => exact (hne rfl).elim
  | cons p rest =>
      apply supportTailValue_upper n b rest _ (hp p (by simp))
      intro q hq
      exact hp q (by simp [hq])

def supportCheck (points : List ExactPoint) (N : Fin 3 → IVec) : Bool :=
  decide (heightRange.hi < (supportRange points (N 0)).lo +
    (supportRange points (N 1)).lo + (supportRange points (N 2)).lo)

theorem supportCheck_sound {N : Fin 3 → IVec} {n : Fin 3 → RVec}
    (hn : ∀ i, ContainsV (N i) (n i)) (points : List ExactPoint)
    (h : supportCheck points N = true) :
    halfRoot < supportValue points (n 0) + supportValue points (n 1) + supportValue points (n 2) := by
  have h0 := (supportRange_sound (hn 0) points).1
  have h1 := (supportRange_sound (hn 1) points).1
  have h2 := (supportRange_sound (hn 2) points).1
  have hh := heightRange_sound.2
  simp only [supportCheck, decide_eq_true_eq] at h
  have h' : (heightRange.hi : ℝ) < (supportRange points (N 0)).lo +
      (supportRange points (N 1)).lo + (supportRange points (N 2)).lo := by exact_mod_cast h
  linarith

/-- Raw indices are checked before constructing any `Fin 3` index. -/
structure RawSegment where
  first : Nat
  second : Nat
  weight : ℚ
  deriving Repr

inductive IntrusionWitness where
  | origin
  | segment (data : RawSegment)
  deriving Repr

def extremeCheck (r : ℚ) (N : Fin 3 → IVec) (B : Fin 3 → Exact.Interval) :
    IntrusionWitness → Bool
  | .origin => decide (0 < r ∧ 0 ≤ (B 0).lo ∧ 0 ≤ (B 1).lo ∧ 0 ≤ (B 2).lo)
  | .segment data =>
      if h : data.first < 3 ∧ data.second < 3 then
        let w : SegmentWitness := ⟨⟨data.first, h.1⟩, ⟨data.second, h.2⟩, data.weight⟩
        decide (0 ≤ w.weight ∧ w.weight ≤ 1 ∧
          (normSqRange (segmentRange (vertexRanges N B) w)).hi < r)
      else false

theorem extremeCheck_sound {r : ℚ} {N : Fin 3 → IVec} {n : Fin 3 → RVec}
    {B : Fin 3 → Exact.Interval} {b : Fin 3 → ℝ}
    (hn : ∀ i, ContainsV (N i) (n i)) (hb : ∀ i, (B i).Contains (b i))
    (hgram : ∀ i j, dot (n i) (n j) = if i = j then 1 else -1/2)
    (hsum : 0 ≤ b 0 + b 1 + b 2) (witness : IntrusionWitness)
    (accepted : extremeCheck r N B witness = true) :
    ∃ q : RVec, InHalfplanes n b q ∧ NI.normSq q.1 q.2 < (r : ℝ) := by
  cases witness with
  | origin =>
      simp only [extremeCheck, decide_eq_true_eq] at accepted
      have hr : (0 : ℝ) < r := by exact_mod_cast accepted.1
      have h0 : (0 : ℝ) ≤ (B 0).lo := by exact_mod_cast accepted.2.1
      have h1 : (0 : ℝ) ≤ (B 1).lo := by exact_mod_cast accepted.2.2.1
      have h2 : (0 : ℝ) ≤ (B 2).lo := by exact_mod_cast accepted.2.2.2
      have hnonneg : ∀ i, 0 ≤ b i := by
        intro i
        fin_cases i
        · exact h0.trans (hb 0).1
        · exact h1.trans (hb 1).1
        · exact h2.trans (hb 2).1
      refine ⟨(0, 0), ?_, ?_⟩
      · intro i
        simpa [dot] using hnonneg i
      · simpa [NI.normSq] using hr
  | segment data =>
      by_cases hi : data.first < 3 ∧ data.second < 3
      · let w : SegmentWitness := ⟨⟨data.first, hi.1⟩, ⟨data.second, hi.2⟩, data.weight⟩
        simp only [extremeCheck, dite_eq_left hi, decide_eq_true_eq] at accepted
        change 0 ≤ w.weight ∧ w.weight ≤ 1 ∧
          (normSqRange (segmentRange (vertexRanges N B) w)).hi < r at accepted
        have hw0 : (0 : ℝ) ≤ w.weight := by exact_mod_cast accepted.1
        have hw1 : (w.weight : ℝ) ≤ 1 := by exact_mod_cast accepted.2.1
        have hupper := (normSqRange_sound
          (segmentRange_sound (vertexRanges_sound hn hb) w)).2
        have hr : ((normSqRange (segmentRange (vertexRanges N B) w)).hi : ℝ) < r :=
          (Rat.cast_lt (K := ℝ)).2 accepted.2.2
        exact ⟨segmentValue (vertexValues n b) w,
          segment_mem (vertex_mem hgram hsum) w hw0 hw1, hupper.trans_lt hr⟩
      · simp [extremeCheck, hi] at accepted

theorem invalid_edge_rejected (r : ℚ) (N : Fin 3 → IVec) (B : Fin 3 → Exact.Interval)
    (data : RawSegment) (h : ¬ (data.first < 3 ∧ data.second < 3)) :
    extremeCheck r N B (.segment data) = false := by simp [extremeCheck, h]

inductive LeafKind where
  | support
  | threeExtremes (witnesses : Fin 3 → IntrusionWitness)

def leafCheck (points : List ExactPoint) (r : ℚ) (C S : Exact.Interval) : LeafKind → Bool
  | .support => supportCheck points (normalRanges C S)
  | .threeExtremes w =>
      let N := normalRanges C S
      let supports := fun i => supportRange points (N i)
      extremeCheck r N (extremeRanges supports 0) (w 0) &&
      extremeCheck r N (extremeRanges supports 1) (w 1) &&
      extremeCheck r N (extremeRanges supports 2) (w 2)

def cellCheck (points : List ExactPoint) (r : ℚ) (cell : Exact.Interval × LeafKind) : Bool :=
  if h : -1 ≤ cell.1.lo ∧ cell.1.hi ≤ 1 then
    leafCheck points r (cosRange cell.1) (sinRange cell.1 h.1 h.2) cell.2
  else false

def OrientationExcluded (points : List ExactPoint) (r : ℚ) (c s : ℝ) : Prop :=
  halfRoot < supportValue points (normalValues c s 0) +
    supportValue points (normalValues c s 1) + supportValue points (normalValues c s 2) ∨
  ∀ k, ∃ q : RVec,
    InHalfplanes (normalValues c s)
      (extremeValues (fun i => supportValue points (normalValues c s i)) k) q ∧
      NI.normSq q.1 q.2 < (r : ℝ)

theorem leafCheck_sound (points : List ExactPoint) (r : ℚ)
    {C S : Exact.Interval} {c s : ℝ} (hc : C.Contains c) (hs : S.Contains s)
    (hunit : c ^ 2 + s ^ 2 = 1) (kind : LeafKind) (h : leafCheck points r C S kind = true) :
    OrientationExcluded points r c s := by
  have hn := normalRanges_sound hc hs
  have hb := fun i => supportRange_sound (hn i) points
  cases kind with
  | support => exact Or.inl (supportCheck_sound hn points h)
  | threeExtremes w =>
      simp only [leafCheck, Bool.and_eq_true] at h
      have hk : ∀ k, extremeCheck r (normalRanges C S)
          (extremeRanges (fun i => supportRange points (normalRanges C S i)) k) (w k) = true := by
        intro k
        fin_cases k
        · exact h.1.1
        · exact h.1.2
        · exact h.2
      right
      intro k
      apply extremeCheck_sound hn (extremeRanges_sound hb k) (normal_dot hunit) _ (w k) (hk k)
      rw [extreme_sum]
      exact halfRoot_pos.le

theorem cellCheck_sound (points : List ExactPoint) (r : ℚ) (cell : Exact.Interval × LeafKind)
    (h : cellCheck points r cell = true) (t : ℝ) (ht : cell.1.Contains t) :
    OrientationExcluded points r (NI.circleX t) (NI.circleY t) := by
  by_cases hb : -1 ≤ cell.1.lo ∧ cell.1.hi ≤ 1
  · simp only [cellCheck, dite_eq_left hb] at h
    exact leafCheck_sound points r (cosRange_sound ht) (sinRange_sound hb.1 hb.2 ht)
      (NI.circle_unit t) cell.2 h
  · simp [cellCheck, hb] at h

structure Certificate where
  cells : List (Exact.Interval × LeafKind)
  frontier : List Exact.Interval

/-- The radius argument is squared. All guards are checked against the actual input list. -/
def check (points : List ExactPoint) (radiusSquared : ℚ) (cert : Certificate) : Bool :=
  !points.isEmpty && decide (0 < radiusSquared) && cert.frontier.isEmpty &&
    partitionFrom (-1) 1 (cert.cells.map Prod.fst) &&
    cert.cells.all (cellCheck points radiusSquared)

theorem empty_points_rejected (r : ℚ) (cert : Certificate) : check [] r cert = false := by
  simp [check]

theorem nonpositive_radius_rejected (points : List ExactPoint) (r : ℚ) (cert : Certificate)
    (hr : r ≤ 0) : check points r cert = false := by
  have h : ¬ 0 < r := not_lt.mpr hr
  simp [check, h]

theorem frontier_rejected (points : List ExactPoint) (r : ℚ) (cert : Certificate)
    (hf : cert.frontier ≠ []) : check points r cert = false := by
  have h : cert.frontier.isEmpty = false := List.isEmpty_eq_false_iff.mpr hf
  simp [check, h]

theorem accepted_nonempty {points : List ExactPoint} {r : ℚ} {cert : Certificate}
    (accepted : check points r cert = true) : points ≠ [] := by
  intro h
  subst points
  simp [check] at accepted

theorem check_orientation {points : List ExactPoint} {r : ℚ} {cert : Certificate}
    (accepted : check points r cert = true) (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    OrientationExcluded points r (NI.circleX t) (NI.circleY t) := by
  simp only [check, Bool.and_eq_true] at accepted
  rcases accepted with ⟨⟨⟨⟨_, _⟩, _⟩, hpartition⟩, hall⟩
  obtain ⟨I, hI, htI⟩ := partitionFrom_sound (cert.cells.map Prod.fst) (-1) 1
    hpartition (by norm_num) t (by simpa using ht)
  obtain ⟨cell, hcell, heq⟩ := List.mem_map.mp hI
  subst I
  exact cellCheck_sound points r cell ((List.all_eq_true.mp hall) cell hcell) t htI

/-- Complete generic consumer: accepted cells force intrusion by an actual arbitrary
unit triangle containing the exact obligation list. No orientation premise is supplied. -/
theorem check_sound {points : List ExactPoint} {r : ℚ} {cert : Certificate}
    (accepted : check points r cert = true) (T : UnitTriangle)
    (contained : ∀ p ∈ points, toPlane p ∈ T.region) :
    ∃ p ∈ T.region, ‖p‖ ^ 2 < (r : ℝ) := by
  have hne := accepted_nonempty accepted
  obtain ⟨c, s, b, hc, hu, hsum, hmem⟩ := TriangleFrame.exists_normal_frame T
  have hpoints : ∀ i p, p ∈ points → dot (normalValues c s i) (pointValue p) ≤ b i := by
    intro i p hp
    have h := (hmem (toPlane p)).mp (contained p hp) i
    simpa only [toPlane, point_coord_zero, point_coord_one, pointValue] using h
  have hs : ∀ i, supportValue points (normalValues c s i) ≤ b i := by
    intro i
    exact supportValue_upper points hne _ _ (hpoints i)
  obtain ⟨t, ht, hct, hst⟩ := NI.semicircle_parameterization hu hc
  have horient := check_orientation accepted t ht
  rw [hct, hst] at horient
  rcases horient with hgap | hext
  · exfalso
    linarith [hs 0, hs 1, hs 2]
  · obtain ⟨q, hq, hnorm⟩ := all_offsets_intersect_open_disk hs hsum hext
    refine ⟨point q.1 q.2, ?_, ?_⟩
    · apply (hmem _).mpr
      simpa only [point_coord_zero, point_coord_one, Prod.eta] using hq
    · rw [norm_point_sq]
      exact hnorm

theorem nonintrusion_impossible {points : List ExactPoint} {r : ℚ} {cert : Certificate}
    (accepted : check points r cert = true) (T : UnitTriangle)
    (contained : ∀ p ∈ points, toPlane p ∈ T.region)
    (nonintrusion : ∀ p ∈ T.region, (r : ℝ) ≤ ‖p‖ ^ 2) : False := by
  obtain ⟨p, hp, hnorm⟩ := check_sound accepted T contained
  exact (not_le_of_gt hnorm) (nonintrusion p hp)

/-- Adapts the already source-bound pilot payload without altering any weights. -/
def pilotKind : NICertificate.LeafKind → LeafKind
  | .support => .support
  | .threeExtremes w => .threeExtremes fun k =>
      .segment ⟨(w k).first.val, (w k).second.val, (w k).weight⟩

def pilotCertificate : Certificate :=
  ⟨NICertificate.q25Certificate.map (fun cell => (cell.1, pilotKind cell.2)), []⟩

def pilotPoints : List ExactPoint :=
  [fromXYZ (-1/2) 0 (1/2), fromXYZ (-1) 0 0, fromXYZ (-1/2) 0 0]

/- The same 23 original cells also pass the generalized list/radius consumer. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem pilot_check : check pilotPoints (1/4) pilotCertificate = true := by
  decide +kernel

end HexagonCover.GenericNI
