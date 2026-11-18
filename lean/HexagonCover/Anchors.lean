import HexagonCover.Geometry

/-!
# Ownership lemmas for actual covering triangles

These general lemmas are conditional on explicitly stated separation or local
coverage hypotheses. They do not assert that all such hypotheses have been
established for the regular hexagon.
-/

namespace HexagonCover

theorem hexVertex_smul (s : ℝ) (i : Fin 6) : hexVertex s i = s • hexVertex 1 i := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [hexVertex, point] <;> ring

theorem hexVertex_unit_norm (i : Fin 6) : ‖hexVertex 1 i‖ = 1 := by
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsq : ‖hexVertex 1 i‖ ^ 2 = 1 := by
    fin_cases i <;> norm_num [hexVertex, norm_point_sq] <;> nlinarith
  nlinarith [norm_nonneg (hexVertex 1 i)]

theorem hexVertex_norm (s : ℝ) (hs : 0 ≤ s) (i : Fin 6) : ‖hexVertex s i‖ = s := by
  rw [hexVertex_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
    hexVertex_unit_norm, mul_one]

/-- Distinct hexagon vertices are separated by at least one side length. -/
theorem hexVertex_dist_sq_lower (s : ℝ) (i j : Fin 6) (hij : i ≠ j) :
    s ^ 2 ≤ dist (hexVertex s i) (hexVertex s j) ^ 2 := by
  have hsqrt : (Real.sqrt 3 * s) ^ 2 = 3 * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  fin_cases i <;> fin_cases j <;> simp_all [hexVertex, dist_point_sq] <;>
    nlinarith [sq_nonneg s]

theorem hexVertex_dist_gt_one {s : ℝ} (hs : 1 < s)
    (i j : Fin 6) (hij : i ≠ j) : 1 < dist (hexVertex s i) (hexVertex s j) := by
  have hd := hexVertex_dist_sq_lower s i j hij
  have hnonneg : 0 ≤ dist (hexVertex s i) (hexVertex s j) := dist_nonneg
  nlinarith

/-- The four nonhorizontal vertices contain the centered coordinate rectangle. -/
theorem mem_hexagon_of_coordinate_bounds {s : ℝ} (hs : 0 < s) {p : Plane}
    (hx : -s / 2 ≤ p 0 ∧ p 0 ≤ s / 2)
    (hy : -Real.sqrt 3 * s / 2 ≤ p 1 ∧ p 1 ≤ Real.sqrt 3 * s / 2) :
    p ∈ Hexagon s := by
  let d : Fin 2 → ℝ := ![s / 2, Real.sqrt 3 * s / 2]
  let S : Set (Fin 2 → ℝ) := Set.univ.pi (fun i => {-(d i), d i})
  let f : (Fin 2 → ℝ) →ₗ[ℝ] Plane :=
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap
  have hcorners : S ⊆ f ⁻¹' Hexagon s := by
    intro z hz
    change ∀ i ∈ (Set.univ : Set (Fin 2)), z i ∈ {-(d i), d i} at hz
    have hz0 := hz 0 (Set.mem_univ _)
    have hz1 := hz 1 (Set.mem_univ _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz0 hz1
    change f z ∈ Hexagon s
    have heq : f z = point (z 0) (z 1) := by
      ext i
      fin_cases i <;> rfl
    rw [heq]
    rcases hz0 with hz0 | hz0 <;> rcases hz1 with hz1 | hz1
    · rw [hz0, hz1]
      simpa [hexVertex, d, neg_div] using hexVertex_mem s (4 : Fin 6)
    · rw [hz0, hz1]
      simpa [hexVertex, d, neg_div] using hexVertex_mem s (2 : Fin 6)
    · rw [hz0, hz1]
      simpa [hexVertex, d, neg_div] using hexVertex_mem s (5 : Fin 6)
    · rw [hz0, hz1]
      simpa [hexVertex, d, neg_div] using hexVertex_mem s (1 : Fin 6)
  have hHull := convexHull_min hcorners ((convex_hexagon s).linear_preimage f)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    fin_cases i <;> simp [d] <;> positivity
  have hpHull : WithLp.ofLp p ∈ convexHull ℝ S := by
    change WithLp.ofLp p ∈ convexHull ℝ (Set.univ.pi (fun i => {-(d i), d i}))
    rw [convexHull_pi]
    intro i _
    change p i ∈ convexHull ℝ {-(d i), d i}
    rw [convexHull_pair, segment_eq_Icc (by linarith [hd i] : -(d i) ≤ d i)]
    fin_cases i
    · simpa [d, neg_div] using hx
    · simpa [d, neg_div] using hy
  exact hHull hpHull

/-- The center really is an interior point of the canonical regular hexagon. -/
theorem zero_mem_interior_hexagon {s : ℝ} (hs : 0 < s) :
    (0 : Plane) ∈ interior (Hexagon s) := by
  let U : Set Plane := {p | p 0 ∈ Set.Ioo (-s / 2) (s / 2) ∧
    p 1 ∈ Set.Ioo (-Real.sqrt 3 * s / 2) (Real.sqrt 3 * s / 2)}
  have hU : IsOpen U := by
    exact (isOpen_Ioo.preimage (by fun_prop : Continuous (fun p : Plane => p 0))).inter
      (isOpen_Ioo.preimage (by fun_prop : Continuous (fun p : Plane => p 1)))
  have hzero : (0 : Plane) ∈ U := by
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    change (-s / 2 < 0 ∧ 0 < s / 2) ∧
      (-Real.sqrt 3 * s / 2 < 0 ∧ 0 < Real.sqrt 3 * s / 2)
    constructor <;> constructor <;> nlinarith [mul_pos hsqrt hs]
  have hsub : U ⊆ Hexagon s := by
    intro p hp
    exact mem_hexagon_of_coordinate_bounds hs ⟨hp.1.1.le, hp.1.2.le⟩
      ⟨hp.2.1.le, hp.2.2.le⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hzero) hsub)

/-- A unit-radius vertex is farther than one from every other outer vertex
when the hexagon side is greater than one. -/
theorem unitVertex_dist_other_gt_one {s : ℝ} (hs : 1 < s)
    (i j : Fin 6) (hij : i ≠ j) : 1 < dist (hexVertex 1 i) (hexVertex s j) := by
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hbound : s ^ 2 - s + 1 ≤ dist (hexVertex 1 i) (hexVertex s j) ^ 2 := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | skip
    all_goals simp [hexVertex, dist_point_sq]
    all_goals ring_nf
    all_goals try simp only [hsqrt]
    all_goals nlinarith
  have hn : 0 ≤ dist (hexVertex 1 i) (hexVertex s j) := dist_nonneg
  nlinarith

/-- Scaling a hexagon vertex inward gives an interior point, conditional only
on the center being interior. -/
theorem unitVertex_mem_interior_of_center {s : ℝ} (hs : 1 < s)
    (hcenter : (0 : Plane) ∈ interior (Hexagon s)) (i : Fin 6) :
    hexVertex 1 i ∈ interior (Hexagon s) := by
  have hspos : 0 < s := by linarith
  have ha : 0 < 1 - 1 / s := sub_pos.mpr ((div_lt_one hspos).mpr hs)
  have hb : 0 ≤ 1 / s := le_of_lt (one_div_pos.mpr hspos)
  have h := (convex_hexagon s).combo_interior_self_mem_interior hcenter
    (hexVertex_mem s i) ha hb (by ring : (1 - 1 / s) + 1 / s = 1)
  rw [hexVertex_smul s i] at h
  simpa [smul_smul, hspos.ne'] using h


/-- Seven anchors separated by more than one have distinct actual covering
triangles. Since there are exactly seven triangles, the assignment is a
permutation. -/
theorem anchor_assignment (config : Fin 7 → UnitTriangle) (a : Fin 7 → Plane)
    (hcover : ∀ i, ∃ j, a i ∈ (config j).region)
    (hsep : ∀ i j, i ≠ j → 1 < dist (a i) (a j)) :
    ∃ σ : Equiv.Perm (Fin 7), ∀ i, a i ∈ (config (σ i)).region := by
  classical
  choose f hf using hcover
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hj : a j ∈ (config (f i)).region := by simpa only [hij] using hf j
    have hd := (config (f i)).dist_le_one (hf i) hj
    exact (not_le_of_gt (hsep i j hne)) hd
  exact ⟨Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, hf⟩

/-- If all other actual triangles own anchors too far from a ball, local
coverage forces that whole open ball into the selected actual triangle. -/
theorem ball_subset_owner_of_anchor_separation
    (config : Fin 7 → UnitTriangle) (a : Fin 7 → Plane)
    (hanchors : ∀ j, a j ∈ (config j).region)
    (q : Plane) (r : ℝ) (i : Fin 7)
    (hcover : Metric.ball q r ⊆ ⋃ j, (config j).region)
    (hsep : ∀ j, j ≠ i → 1 + r ≤ dist q (a j)) :
    Metric.ball q r ⊆ (config i).region := by
  intro p hp
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hp)
  by_cases hji : j = i
  · simpa only [hji] using hj
  · have hd := (config j).dist_le_one hj (hanchors j)
    have ht := dist_triangle q p (a j)
    have hp' : dist q p < r := by simpa only [Metric.mem_ball, dist_comm] using hp
    have hs := hsep j hji
    linarith

/-- A triangle containing a positive open disk about the center cannot contain
any point on the unit circle. This uses the disk in this very same triangle. -/
theorem unit_circle_not_mem_of_center_disk (T : UnitTriangle) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball (0 : Plane) r ⊆ T.region)
    {u : Plane} (hu : ‖u‖ = 1) : u ∉ T.region := by
  intro huT
  have hp : (-r / 2) • u ∈ Metric.ball (0 : Plane) r := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hu,
      mul_one, abs_of_neg (by linarith : -r / 2 < 0)]
    linarith
  have hd := T.dist_le_one huT (hball hp)
  have he : u - (-r / 2) • u = (1 + r / 2) • u := by module
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 1 + r / 2), hu, mul_one] at hd
  linarith

/-- Conditional local ownership for a finite closed cover. If a point is
interior to the covered region and is excluded from the other six actual
triangles, a positive disk around it lies in the selected actual triangle. -/
theorem exists_ball_subset_owner
    (config : Fin 7 → UnitTriangle) (H : Set Plane)
    (hcover : H ⊆ ⋃ j, (config j).region)
    (q : Plane) (i : Fin 7) (hq : q ∈ interior H)
    (hexclude : ∀ j, j ≠ i → q ∉ (config j).region) :
    ∃ r > 0, Metric.ball q r ⊆ (config i).region := by
  let U : Set Plane := interior H ∩
    ⋂ j : {j : Fin 7 // j ≠ i}, ((config j.val).region)ᶜ
  have hU : IsOpen U :=
    isOpen_interior.inter (isOpen_iInter_of_finite fun j => (config j.val).closed_region.isOpen_compl)
  have hqU : q ∈ U := by
    refine ⟨hq, Set.mem_iInter.mpr ?_⟩
    intro j
    exact hexclude j.val j.property
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU q hqU
  refine ⟨r, hr, ?_⟩
  intro p hp
  have hpU := hsub hp
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (interior_subset hpU.1))
  by_cases hji : j = i
  · simpa only [hji] using hj
  · exact False.elim ((Set.mem_iInter.mp hpU.2 ⟨j, hji⟩) hj)

/-- Strict separation from all competing assigned anchors provides a positive
same-owner disk at an interior point of the covered set. -/
theorem exists_ball_subset_owner_of_strict_separation
    (config : Fin 7 → UnitTriangle) (a : Fin 7 → Plane)
    (hanchors : ∀ j, a j ∈ (config j).region)
    (H : Set Plane) (hcover : H ⊆ ⋃ j, (config j).region)
    (q : Plane) (i : Fin 7) (hq : q ∈ interior H)
    (hsep : ∀ j, j ≠ i → 1 < dist q (a j)) :
    ∃ r > 0, Metric.ball q r ⊆ (config i).region := by
  apply exists_ball_subset_owner config H hcover q i hq
  intro j hji hqj
  exact (not_le_of_gt (hsep j hji)) ((config j).dist_le_one hqj (hanchors j))

/-- A convenient same-piece disk upgrade. A center disk excludes the center
triangle from every unit-circle point; separation from the other anchors then
excludes the remaining triangles. -/
theorem exists_ball_subset_vertex_owner
    (config : Fin 7 → UnitTriangle) (a : Fin 7 → Plane)
    (hanchors : ∀ j, a j ∈ (config j).region)
    (H : Set Plane) (hcover : H ⊆ ⋃ j, (config j).region)
    (center owner : Fin 7) (_hne : owner ≠ center)
    (r : ℝ) (hr : 0 < r)
    (hcenter : Metric.ball (0 : Plane) r ⊆ (config center).region)
    (u : Plane) (hu : ‖u‖ = 1) (huint : u ∈ interior H)
    (hsep : ∀ j, j ≠ owner → j ≠ center → 1 < dist u (a j)) :
    ∃ ε > 0, Metric.ball u ε ⊆ (config owner).region := by
  apply exists_ball_subset_owner config H hcover u owner huint
  intro j hj
  by_cases hjc : j = center
  · subst j
    exact unit_circle_not_mem_of_center_disk (config center) r hr hcenter hu
  · intro huj
    exact (not_le_of_gt (hsep j hj hjc)) ((config j).dist_le_one huj (hanchors j))

/-- The seven outer anchors: the center followed by the six outer vertices. -/
noncomputable def outerAnchor (s : ℝ) : Fin 7 → Plane := Fin.cases 0 (hexVertex s)

@[simp] theorem outerAnchor_zero (s : ℝ) : outerAnchor s 0 = 0 := rfl
@[simp] theorem outerAnchor_succ (s : ℝ) (i : Fin 6) :
    outerAnchor s i.succ = hexVertex s i := rfl

theorem outerAnchor_mem {s : ℝ} (hs : 0 < s) (i : Fin 7) :
    outerAnchor s i ∈ Hexagon s := by
  cases i using Fin.cases with
  | zero => exact interior_subset (zero_mem_interior_hexagon hs)
  | succ i => exact hexVertex_mem s i

theorem outerAnchor_separated {s : ℝ} (hs : 1 < s)
    (i j : Fin 7) (hij : i ≠ j) : 1 < dist (outerAnchor s i) (outerAnchor s j) := by
  have hs0 : 0 ≤ s := by linarith
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => simpa [dist_zero_left, hexVertex_norm s hs0] using hs
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa [dist_zero_right, hexVertex_norm s hs0] using hs
    | succ j =>
      exact hexVertex_dist_gt_one hs i j (by
        intro heq
        exact hij (congrArg Fin.succ heq))

/-- Full anchor reduction for the exact regular hexagon. Every assumed cover
has a permutation assigning the seven outer anchors to distinct actual
triangles; positive disks about the center and six unit-radius points lie in
those very same assigned triangles. This is a proved reduction, not a proof
that the resulting disk configuration is impossible. -/
theorem anchor_disks_of_cover {s : ℝ} (hs : 1 < s)
    (config : Fin 7 → UnitTriangle) (hcover : Covers s config) :
    ∃ σ : Equiv.Perm (Fin 7),
      (∀ i, outerAnchor s i ∈ (config (σ i)).region) ∧
      (∀ i, ∃ r > 0, Metric.ball (outerAnchor 1 i) r ⊆ (config (σ i)).region) := by
  have hs0 : 0 < s := by linarith
  have hanc : ∀ i, ∃ j, outerAnchor s i ∈ (config j).region := by
    intro i
    exact Set.mem_iUnion.mp (hcover (outerAnchor_mem hs0 i))
  obtain ⟨σ, hσ⟩ := anchor_assignment config (outerAnchor s) hanc
    (outerAnchor_separated hs)
  have hcoverσ : Hexagon s ⊆ ⋃ i, (config (σ i)).region := by
    intro p hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hp)
    obtain ⟨i, rfl⟩ := σ.surjective j
    exact Set.mem_iUnion.mpr ⟨i, hj⟩
  have hcenterInt := zero_mem_interior_hexagon hs0
  obtain ⟨r, hr, hcenter⟩ := exists_ball_subset_owner_of_strict_separation
    (fun i => config (σ i)) (outerAnchor s) hσ (Hexagon s) hcoverσ 0 0 hcenterInt
    (by
      intro j hj
      simpa using outerAnchor_separated hs (0 : Fin 7) j (Ne.symm hj))
  refine ⟨σ, hσ, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨r, hr, hcenter⟩
  | succ i =>
    apply exists_ball_subset_vertex_owner (fun j => config (σ j)) (outerAnchor s) hσ
      (Hexagon s) hcoverσ 0 i.succ (Fin.succ_ne_zero i) r hr hcenter
      (hexVertex 1 i) (hexVertex_unit_norm i)
      (unitVertex_mem_interior_of_center hs hcenterInt i)
    intro j hji hj0
    cases j using Fin.cases with
    | zero => exact (hj0 rfl).elim
    | succ j =>
      exact unitVertex_dist_other_gt_one hs i j (by
        intro heq
        exact hji (congrArg Fin.succ heq.symm))

end HexagonCover
