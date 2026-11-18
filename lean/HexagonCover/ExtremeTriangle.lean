import HexagonCover.NICertificate

/-! Scalar geometry connecting the checked interval certificate to halfplane triangles. -/

namespace HexagonCover.ExtremeTriangle

open NICertificate

theorem halfRoot_sq : halfRoot ^ 2 = 3/4 := by
  unfold halfRoot
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem halfRoot_pos : 0 < halfRoot := by
  unfold halfRoot
  positivity

theorem normal_dot {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1) (i j : Fin 3) :
    dot (normalValues c s i) (normalValues c s j) = if i = j then 1 else -1/2 := by
  have hc := congrArg (fun z : ℝ => c ^ 2 * z) halfRoot_sq
  have hs := congrArg (fun z : ℝ => s ^ 2 * z) halfRoot_sq
  fin_cases i <;> fin_cases j <;> norm_num [normalValues, dot] <;> nlinarith

theorem normal_sum_x (c s : ℝ) :
    (normalValues c s 0).1 + (normalValues c s 1).1 + (normalValues c s 2).1 = 0 := by
  simp [normalValues]
  ring

theorem normal_sum_y (c s : ℝ) :
    (normalValues c s 0).2 + (normalValues c s 1).2 + (normalValues c s 2).2 = 0 := by
  simp [normalValues]
  ring

/-- A second unit normal at dot product -1/2 has one of the two required orientations. -/
theorem other_normal_eq {c s u v : ℝ} (hbase : c ^ 2 + s ^ 2 = 1)
    (hother : u ^ 2 + v ^ 2 = 1) (hdot : c * u + s * v = -1/2) :
    (u, v) = normalValues c s 1 ∨ (u, v) = normalValues c s 2 := by
  have hidentity : (c * u + s * v) ^ 2 + (c * v - s * u) ^ 2 =
      (c ^ 2 + s ^ 2) * (u ^ 2 + v ^ 2) := by ring
  rw [hdot, hbase, hother] at hidentity
  have hdet : (c * v - s * u) ^ 2 = halfRoot ^ 2 := by nlinarith [halfRoot_sq]
  have hrecx : c * (c * u + s * v) - s * (c * v - s * u) = u := by
    nlinarith [congrArg (fun z : ℝ => z * u) hbase]
  have hrecy : s * (c * u + s * v) + c * (c * v - s * u) = v := by
    nlinarith [congrArg (fun z : ℝ => z * v) hbase]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdet with hp | hn
  · rw [hdot, hp] at hrecx hrecy
    left
    apply Prod.ext <;> norm_num [normalValues] <;> nlinarith
  · rw [hdot, hn] at hrecx hrecy
    right
    apply Prod.ext <;> norm_num [normalValues] <;> nlinarith

def InHalfplanes (n : Fin 3 → RVec) (b : Fin 3 → ℝ) (q : RVec) : Prop :=
  ∀ i, dot (n i) q ≤ b i

theorem intersection_dot {n : Fin 3 → RVec} {b : Fin 3 → ℝ}
    (hn : ∀ i j, dot (n i) (n j) = if i = j then 1 else -1/2)
    (r i j : Fin 3) :
    dot (n r) (intersectionValue n b i j) =
      coefficientValue b i j * (if r = i then 1 else -1/2) +
      coefficientValue b j i * (if r = j then 1 else -1/2) := by
  calc
    _ = coefficientValue b i j * dot (n r) (n i) +
        coefficientValue b j i * dot (n r) (n j) := by
      unfold dot intersectionValue
      ring
    _ = _ := by rw [hn, hn]

theorem vertex_mem {n : Fin 3 → RVec} {b : Fin 3 → ℝ}
    (hn : ∀ i j, dot (n i) (n j) = if i = j then 1 else -1/2)
    (hb : 0 ≤ b 0 + b 1 + b 2) (v : Fin 3) :
    InHalfplanes n b (vertexValues n b v) := by
  intro r
  fin_cases v <;> fin_cases r <;>
    norm_num [vertexValues, vertexSides, intersection_dot hn, coefficientValue] <;> linarith

theorem segment_mem {n : Fin 3 → RVec} {b : Fin 3 → ℝ} {v : Fin 3 → RVec}
    (hv : ∀ i, InHalfplanes n b (v i)) (w : SegmentWitness)
    (hwlo : 0 ≤ (w.weight : ℝ)) (hwhi : (w.weight : ℝ) ≤ 1) :
    InHalfplanes n b (segmentValue v w) := by
  intro i
  calc
    _ = (1 - (w.weight : ℝ)) * dot (n i) (v w.first) +
        (w.weight : ℝ) * dot (n i) (v w.second) := by
      unfold dot segmentValue
      ring
    _ ≤ (1 - (w.weight : ℝ)) * b i + (w.weight : ℝ) * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hv w.first i) (sub_nonneg.mpr hwhi))
        (mul_le_mul_of_nonneg_left (hv w.second i) hwlo)
    _ = b i := by ring

theorem extreme_sum (s : Fin 3 → ℝ) (k : Fin 3) :
    extremeValues s k 0 + extremeValues s k 1 + extremeValues s k 2 = halfRoot := by
  fin_cases k <;> norm_num [extremeValues, otherSides] <;> ring

theorem extremeValues_eq (s : Fin 3 → ℝ) (k j : Fin 3) :
    extremeValues s k j = s j +
      (if j = k then halfRoot - (s 0 + s 1 + s 2) else 0) := by
  fin_cases k <;> fin_cases j <;> norm_num [extremeValues, otherSides] <;> ring

theorem extreme_segment_mem {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1)
    (k : Fin 3) (w : SegmentWitness)
    (hwlo : 0 ≤ (w.weight : ℝ)) (hwhi : (w.weight : ℝ) ≤ 1) :
    InHalfplanes (normalValues c s) (extremeValues (supportValues (normalValues c s)) k)
      (extremeSegmentValue c s k w) := by
  apply segment_mem _ w hwlo hwhi
  intro i
  apply vertex_mem (normal_dot hunit)
  rw [extreme_sum]
  exact halfRoot_pos.le

noncomputable def slack (s : Fin 3 → ℝ) : ℝ := halfRoot - (s 0 + s 1 + s 2)

theorem blend_extremes {a : Fin 3 → ℝ} (ha : a 0 + a 1 + a 2 = 1)
    (s : Fin 3 → ℝ) (j : Fin 3) :
    a 0 * extremeValues s 0 j + a 1 * extremeValues s 1 j + a 2 * extremeValues s 2 j =
      s j + a j * slack s := by
  have h0 := congrArg (fun z : ℝ => z * s 0) ha
  have h1 := congrArg (fun z : ℝ => z * s 1) ha
  have h2 := congrArg (fun z : ℝ => z * s 2) ha
  fin_cases j <;> norm_num [extremeValues_eq, slack] <;> nlinarith

/-- All feasible offsets, including zero slack, are combinations of the three extremes. -/
theorem offsets_decomposition {s b : Fin 3 → ℝ}
    (hs : ∀ i, s i ≤ b i) (hb : b 0 + b 1 + b 2 = halfRoot) :
    ∃ a : Fin 3 → ℝ, (∀ i, 0 ≤ a i) ∧ a 0 + a 1 + a 2 = 1 ∧
      ∀ j, b j = a 0 * extremeValues s 0 j + a 1 * extremeValues s 1 j +
        a 2 * extremeValues s 2 j := by
  have hd : 0 ≤ slack s := by
    unfold slack
    linarith [hs 0, hs 1, hs 2]
  by_cases hz : slack s = 0
  · have heq : ∀ j, b j = s j := by
      have hz' : halfRoot - (s 0 + s 1 + s 2) = 0 := hz
      intro j
      fin_cases j <;> dsimp <;> linarith [hs 0, hs 1, hs 2]
    refine ⟨![1, 0, 0], ?_, by norm_num, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro j
      rw [blend_extremes (by norm_num), hz, mul_zero, add_zero]
      exact heq j
  · let a : Fin 3 → ℝ := fun i => (b i - s i) / slack s
    have hsum : a 0 + a 1 + a 2 = 1 := by
      dsimp [a]
      rw [← add_div, ← add_div]
      apply (div_eq_iff hz).2
      unfold slack
      linarith
    have had (i : Fin 3) : a i * slack s = b i - s i := by
      exact div_mul_cancel₀ _ hz
    refine ⟨a, ?_, hsum, ?_⟩
    · intro i
      exact div_nonneg (sub_nonneg.mpr (hs i)) hd
    · intro j
      rw [blend_extremes hsum, had j]
      ring

def blendPoint (a : Fin 3 → ℝ) (q : Fin 3 → RVec) : RVec :=
  (a 0 * (q 0).1 + a 1 * (q 1).1 + a 2 * (q 2).1,
   a 0 * (q 0).2 + a 1 * (q 1).2 + a 2 * (q 2).2)

theorem blend_mem {a : Fin 3 → ℝ} {q : Fin 3 → RVec}
    {n : Fin 3 → RVec} {s b : Fin 3 → ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (hq : ∀ k, InHalfplanes n (extremeValues s k) (q k))
    (hb : ∀ j, b j = a 0 * extremeValues s 0 j + a 1 * extremeValues s 1 j +
      a 2 * extremeValues s 2 j) : InHalfplanes n b (blendPoint a q) := by
  intro i
  calc
    _ = a 0 * dot (n i) (q 0) + a 1 * dot (n i) (q 1) + a 2 * dot (n i) (q 2) := by
      unfold blendPoint dot
      ring
    _ ≤ a 0 * extremeValues s 0 i + a 1 * extremeValues s 1 i +
        a 2 * extremeValues s 2 i :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hq 0 i) (ha 0))
        (mul_le_mul_of_nonneg_left (hq 1 i) (ha 1)))
        (mul_le_mul_of_nonneg_left (hq 2 i) (ha 2))
    _ = b i := (hb i).symm

theorem all_offsets_intersect_open_disk {n : Fin 3 → RVec} {s b : Fin 3 → ℝ} {r : ℝ}
    (hs : ∀ i, s i ≤ b i) (hb : b 0 + b 1 + b 2 = halfRoot)
    (hext : ∀ k, ∃ q : RVec, InHalfplanes n (extremeValues s k) q ∧ NI.normSq q.1 q.2 < r) :
    ∃ q : RVec, InHalfplanes n b q ∧ NI.normSq q.1 q.2 < r := by
  classical
  choose q hmem hnorm using hext
  obtain ⟨a, ha, hsum, hblend⟩ := offsets_decomposition hs hb
  refine ⟨blendPoint a q, blend_mem ha hmem hblend, ?_⟩
  exact NI.three_point_strict_bound (ha 0) (ha 1) (ha 2) hsum (hnorm 0) (hnorm 1) (hnorm 2)

theorem supports_bounded {n : Fin 3 → RVec} {b : Fin 3 → ℝ}
    (hpoints : ∀ i j, dot (n i) (pointValues j) ≤ b i) : ∀ i, supportValues n i ≤ b i := by
  intro i
  exact max_le (max_le (hpoints i 0) (hpoints i 1)) (hpoints i 2)

/-- The original 23-cell certificate excludes every feasible normalized halfplane triangle.
This theorem consumes its kernel-checked interval certificate and its strict radius bounds. -/
theorem q25_scalar_invasion {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 ≤ c)
    (b : Fin 3 → ℝ) (hb : b 0 + b 1 + b 2 = halfRoot)
    (hpoints : ∀ i j, dot (normalValues c s i) (pointValues j) ≤ b i) :
    ∃ q : RVec, InHalfplanes (normalValues c s) b q ∧ NI.normSq q.1 q.2 < 1/4 := by
  obtain ⟨t, ht, hct, hst⟩ := NI.semicircle_parameterization hunit hc
  obtain ⟨kind, hkind⟩ := q25_continuous_certificate t ht
  rw [hct, hst] at hkind
  have hs := supports_bounded hpoints
  cases kind with
  | support =>
      change halfRoot < supportValues (normalValues c s) 0 +
        supportValues (normalValues c s) 1 + supportValues (normalValues c s) 2 at hkind
      exfalso
      linarith [hs 0, hs 1, hs 2]
  | threeExtremes w =>
      apply all_offsets_intersect_open_disk hs hb
      intro k
      have hk := hkind k
      exact ⟨extremeSegmentValue c s k (w k),
        extreme_segment_mem hunit k (w k) hk.1 hk.2.1, hk.2.2⟩

end HexagonCover.ExtremeTriangle
