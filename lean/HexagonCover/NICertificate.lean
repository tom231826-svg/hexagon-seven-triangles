import HexagonCover.Exact
import HexagonCover.NI

/-!
Independent Lean consumer foundations for the frozen Q25 fact 7211 interval
certificate. The mathematical specification `two-ni-method.md` and the frozen
JSON certificate were read; no previous Python geometry functions were imported
or copied. Certificate status strings are not assumptions.
-/

namespace HexagonCover.NICertificate

open Exact

def partitionFrom (a b : ℚ) : List Interval → Bool
  | [] => decide (a = b)
  | I :: rest => decide (I.lo = a ∧ I.lo < I.hi) && partitionFrom I.hi b rest

/-- Adjacent, strictly positive closed cells cover every real point of the domain. -/
theorem partitionFrom_sound (cells : List Interval) (a b : ℚ)
    (h : partitionFrom a b cells = true) (hab : a < b)
    (t : ℝ) (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) :
    ∃ I ∈ cells, I.Contains t := by
  induction cells generalizing a with
  | nil =>
      simp only [partitionFrom, decide_eq_true_eq] at h
      exact (hab.ne h).elim
  | cons I rest ih =>
      simp only [partitionFrom, Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hI : t ≤ (I.hi : ℝ)
      · refine ⟨I, List.mem_cons_self, ?_⟩
        exact ⟨by simpa [h.1.1] using ht.1, hI⟩
      · have hIt : (I.hi : ℝ) < t := lt_of_not_ge hI
        have hIb : I.hi < b := by exact_mod_cast hIt.trans_le ht.2
        obtain ⟨J, hJ, htJ⟩ := ih I.hi h.2 hIb ⟨hIt.le, ht.2⟩
        exact ⟨J, List.mem_cons_of_mem I hJ, htJ⟩

theorem partitionFrom_forall (cells : List Interval) (a b : ℚ)
    (h : partitionFrom a b cells = true) (hab : a < b) (P : ℝ → Prop)
    (hcell : ∀ I ∈ cells, ∀ t, I.Contains t → P t) :
    ∀ t : ℝ, (a : ℝ) ≤ t ∧ t ≤ (b : ℝ) → P t := by
  intro t ht
  obtain ⟨I, hI, htI⟩ := partitionFrom_sound cells a b h hab t ht
  exact hcell I hI t htI

def q25Cells : List Interval := [
  ⟨-1, -7/8, by norm_num⟩,
  ⟨-7/8, -3/4, by norm_num⟩,
  ⟨-3/4, -5/8, by norm_num⟩,
  ⟨-5/8, -1/2, by norm_num⟩,
  ⟨-1/2, -3/8, by norm_num⟩,
  ⟨-3/8, -1/4, by norm_num⟩,
  ⟨-1/4, -1/8, by norm_num⟩,
  ⟨-1/8, -1/16, by norm_num⟩,
  ⟨-1/16, 0, by norm_num⟩,
  ⟨0, 1/32, by norm_num⟩,
  ⟨1/32, 1/16, by norm_num⟩,
  ⟨1/16, 3/32, by norm_num⟩,
  ⟨3/32, 1/8, by norm_num⟩,
  ⟨1/8, 5/32, by norm_num⟩,
  ⟨5/32, 3/16, by norm_num⟩,
  ⟨3/16, 1/4, by norm_num⟩,
  ⟨1/4, 5/16, by norm_num⟩,
  ⟨5/16, 11/32, by norm_num⟩,
  ⟨11/32, 3/8, by norm_num⟩,
  ⟨3/8, 7/16, by norm_num⟩,
  ⟨7/16, 1/2, by norm_num⟩,
  ⟨1/2, 3/4, by norm_num⟩,
  ⟨3/4, 1, by norm_num⟩]

theorem q25_partition_checked : partitionFrom (-1) 1 q25Cells = true := by
  norm_num [partitionFrom, q25Cells]

theorem q25_partition_covers (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    ∃ I ∈ q25Cells, I.Contains t := by
  exact partitionFrom_sound q25Cells (-1) 1 q25_partition_checked (by norm_num) t
    (by simpa using ht)

def sqrt3Interval : Interval :=
  ⟨2195635245840476761639769790215 / 1267650600228229401496703205376,
   2195635245840476761639769790216 / 1267650600228229401496703205376,
   by norm_num⟩

theorem sqrt3Interval_sound : sqrt3Interval.Contains (Real.sqrt 3) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlo : (0 : ℝ) ≤ sqrt3Interval.lo := by norm_num [sqrt3Interval]
  have hhi : (0 : ℝ) ≤ sqrt3Interval.hi := by norm_num [sqrt3Interval]
  have hl : (sqrt3Interval.lo : ℝ) ^ 2 ≤ 3 := by norm_num [sqrt3Interval]
  have hh : (3 : ℝ) ≤ (sqrt3Interval.hi : ℝ) ^ 2 := by norm_num [sqrt3Interval]
  constructor <;> nlinarith

def maximum (I J : Interval) : Interval :=
  ⟨max I.lo J.lo, max I.hi J.hi, max_le_max I.ordered J.ordered⟩

theorem maximum_sound {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (maximum I J).Contains (max x y) := by
  constructor
  · simpa [maximum] using max_le_max hx.1 hy.1
  · simpa [maximum] using max_le_max hx.2 hy.2

theorem square_lo_nonneg (I : Interval) : 0 ≤ (square I).lo := by
  simp only [square]
  split_ifs <;> positivity

theorem ratio_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 - b) / (1 + b) ≤ (1 - a) / (1 + a) := by
  have hb : 0 ≤ b := ha.trans hab
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

def cosRange (I : Interval) : Interval where
  lo := (1 - (square I).hi) / (1 + (square I).hi)
  hi := (1 - (square I).lo) / (1 + (square I).lo)
  ordered := by
    have hl := square_lo_nonneg I
    have hh := hl.trans (square I).ordered
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [(square I).ordered]

theorem cosRange_sound {I : Interval} {t : ℝ} (ht : I.Contains t) :
    (cosRange I).Contains (NI.circleX t) := by
  have hs := square_contains ht
  have hl : (0 : ℝ) ≤ (square I).lo := by exact_mod_cast square_lo_nonneg I
  constructor
  · simpa [cosRange, NI.circleX] using ratio_antitone (sq_nonneg t) hs.2
  · simpa [cosRange, NI.circleX] using ratio_antitone hl hs.1

theorem circleY_monotone {a b : ℝ} (ha : -1 ≤ a ∧ a ≤ 1)
    (hb : -1 ≤ b ∧ b ≤ 1) (hab : a ≤ b) : NI.circleY a ≤ NI.circleY b := by
  have hp : a * b ≤ 1 := by
    have h := (product_bounds ha hb).2
    norm_num at h
    exact h
  have hprod : 0 ≤ (b - a) * (1 - a * b) :=
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hp)
  unfold NI.circleY
  apply (div_le_div_iff₀ (NI.circle_den_pos a) (NI.circle_den_pos b)).2
  nlinarith

def sinRange (I : Interval) (hlo : -1 ≤ I.lo) (hhi : I.hi ≤ 1) : Interval where
  lo := (2 * I.lo) / (1 + I.lo ^ 2)
  hi := (2 * I.hi) / (1 + I.hi ^ 2)
  ordered := by
    have ha : -1 ≤ (I.lo : ℝ) ∧ (I.lo : ℝ) ≤ 1 := by
      exact_mod_cast (show -1 ≤ I.lo ∧ I.lo ≤ 1 from ⟨hlo, I.ordered.trans hhi⟩)
    have hb : -1 ≤ (I.hi : ℝ) ∧ (I.hi : ℝ) ≤ 1 := by
      exact_mod_cast (show -1 ≤ I.hi ∧ I.hi ≤ 1 from ⟨hlo.trans I.ordered, hhi⟩)
    have hab : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
    have h := circleY_monotone ha hb hab
    unfold NI.circleY at h
    exact_mod_cast h

theorem sinRange_sound {I : Interval} (hlo : -1 ≤ I.lo) (hhi : I.hi ≤ 1)
    {t : ℝ} (ht : I.Contains t) : (sinRange I hlo hhi).Contains (NI.circleY t) := by
  have hl : (-1 : ℝ) ≤ I.lo := by exact_mod_cast hlo
  have hh : (I.hi : ℝ) ≤ 1 := by exact_mod_cast hhi
  have hab : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  have ha : -1 ≤ (I.lo : ℝ) ∧ (I.lo : ℝ) ≤ 1 := ⟨hl, hab.trans hh⟩
  have hb : -1 ≤ (I.hi : ℝ) ∧ (I.hi : ℝ) ≤ 1 := ⟨hl.trans hab, hh⟩
  have ht' : -1 ≤ t ∧ t ≤ 1 := ⟨hl.trans ht.1, ht.2.trans hh⟩
  constructor
  · simpa [sinRange, NI.circleY] using circleY_monotone ha ht' ht.1
  · simpa [sinRange, NI.circleY] using circleY_monotone ht' hb ht.2

abbrev IVec := Interval × Interval
abbrev RVec := ℝ × ℝ

def ContainsV (v : IVec) (x : RVec) : Prop := v.1.Contains x.1 ∧ v.2.Contains x.2

def addV (v w : IVec) : IVec := (add v.1 w.1, add v.2 w.2)
def scaleV (a : Interval) (v : IVec) : IVec := (mul a v.1, mul a v.2)
def dotRange (v w : IVec) : Interval := add (mul v.1 w.1) (mul v.2 w.2)
def normSqRange (v : IVec) : Interval := add (square v.1) (square v.2)

def dot (v w : RVec) : ℝ := v.1 * w.1 + v.2 * w.2

theorem addV_sound {v w : IVec} {x y : RVec} (hx : ContainsV v x) (hy : ContainsV w y) :
    ContainsV (addV v w) (x.1 + y.1, x.2 + y.2) :=
  ⟨add_contains hx.1 hy.1, add_contains hx.2 hy.2⟩

theorem scaleV_sound {a : Interval} {v : IVec} {r : ℝ} {x : RVec}
    (hr : a.Contains r) (hx : ContainsV v x) :
    ContainsV (scaleV a v) (r * x.1, r * x.2) :=
  ⟨mul_contains hr hx.1, mul_contains hr hx.2⟩

theorem dotRange_sound {v w : IVec} {x y : RVec}
    (hx : ContainsV v x) (hy : ContainsV w y) : (dotRange v w).Contains (dot x y) :=
  add_contains (mul_contains hx.1 hy.1) (mul_contains hx.2 hy.2)

theorem normSqRange_sound {v : IVec} {x : RVec} (hx : ContainsV v x) :
    (normSqRange v).Contains (NI.normSq x.1 x.2) :=
  add_contains (square_contains hx.1) (square_contains hx.2)

noncomputable def halfRoot : ℝ := Real.sqrt 3 / 2
def heightRange : Interval := mul (singleton (1/2)) sqrt3Interval

theorem heightRange_sound : heightRange.Contains halfRoot := by
  simpa [heightRange, halfRoot, div_eq_mul_inv, mul_comm] using
    mul_contains (singleton_contains (1/2)) sqrt3Interval_sound

def normalRanges (C S : Interval) : Fin 3 → IVec := ![
  (C, S),
  (sub (mul (singleton (-1/2)) C) (mul heightRange S),
   add (mul heightRange C) (mul (singleton (-1/2)) S)),
  (add (mul (singleton (-1/2)) C) (mul heightRange S),
   sub (mul (singleton (-1/2)) S) (mul heightRange C))]

noncomputable def normalValues (c s : ℝ) : Fin 3 → RVec := ![
  (c, s),
  ((-1/2) * c - halfRoot * s, halfRoot * c + (-1/2) * s),
  ((-1/2) * c + halfRoot * s, (-1/2) * s - halfRoot * c)]

theorem normalRanges_sound {C S : Interval} {c s : ℝ}
    (hc : C.Contains c) (hs : S.Contains s) (i : Fin 3) :
    ContainsV (normalRanges C S i) (normalValues c s i) := by
  have hnc := mul_contains (singleton_contains (-1/2)) hc
  have hns := mul_contains (singleton_contains (-1/2)) hs
  have hhc := mul_contains heightRange_sound hc
  have hhs := mul_contains heightRange_sound hs
  fin_cases i
  · exact ⟨hc, hs⟩
  · simpa [normalRanges, normalValues, ContainsV] using
      And.intro (sub_contains hnc hhs) (add_contains hhc hns)
  · simpa [normalRanges, normalValues, ContainsV] using
      And.intro (add_contains hnc hhs) (sub_contains hns hhc)

def pointRanges : Fin 3 → IVec := ![
  (singleton (-1/2), heightRange),
  (singleton (-1), singleton 0),
  (singleton (-1/2), singleton 0)]

noncomputable def pointValues : Fin 3 → RVec := ![
  ((-1/2), halfRoot), ((-1), 0), ((-1/2), 0)]

theorem pointRanges_sound (i : Fin 3) : ContainsV (pointRanges i) (pointValues i) := by
  fin_cases i
  · simpa [pointRanges, pointValues, ContainsV] using
      And.intro (singleton_contains (-1/2)) heightRange_sound
  · simpa [pointRanges, pointValues, ContainsV] using
      And.intro (singleton_contains (-1)) (singleton_contains 0)
  · simpa [pointRanges, pointValues, ContainsV] using
      And.intro (singleton_contains (-1/2)) (singleton_contains 0)

def supportRanges (N : Fin 3 → IVec) (i : Fin 3) : Interval :=
  maximum (maximum (dotRange (N i) (pointRanges 0)) (dotRange (N i) (pointRanges 1)))
    (dotRange (N i) (pointRanges 2))

noncomputable def supportValues (N : Fin 3 → RVec) (i : Fin 3) : ℝ :=
  max (max (dot (N i) (pointValues 0)) (dot (N i) (pointValues 1)))
    (dot (N i) (pointValues 2))

theorem supportRanges_sound {N : Fin 3 → IVec} {n : Fin 3 → RVec}
    (hn : ∀ i, ContainsV (N i) (n i)) (i : Fin 3) :
    (supportRanges N i).Contains (supportValues n i) :=
  maximum_sound (maximum_sound (dotRange_sound (hn i) (pointRanges_sound 0))
    (dotRange_sound (hn i) (pointRanges_sound 1)))
    (dotRange_sound (hn i) (pointRanges_sound 2))

def supportCheck (N : Fin 3 → IVec) : Bool :=
  decide (heightRange.hi < (supportRanges N 0).lo +
    (supportRanges N 1).lo + (supportRanges N 2).lo)

theorem supportCheck_sound {N : Fin 3 → IVec} {n : Fin 3 → RVec}
    (hn : ∀ i, ContainsV (N i) (n i)) (h : supportCheck N = true) :
    halfRoot < supportValues n 0 + supportValues n 1 + supportValues n 2 := by
  have h0 := (supportRanges_sound hn 0).1
  have h1 := (supportRanges_sound hn 1).1
  have h2 := (supportRanges_sound hn 2).1
  have hh := heightRange_sound.2
  simp only [supportCheck, decide_eq_true_eq] at h
  have h' : (heightRange.hi : ℝ) < (supportRanges N 0).lo +
      (supportRanges N 1).lo + (supportRanges N 2).lo := by exact_mod_cast h
  linarith

def otherSides : Fin 3 → Fin 3 × Fin 3 := ![(1, 2), (2, 0), (0, 1)]

def extremeRanges (S : Fin 3 → Interval) (k j : Fin 3) : Interval :=
  if j = k then sub heightRange (add (S (otherSides k).1) (S (otherSides k).2)) else S j

noncomputable def extremeValues (s : Fin 3 → ℝ) (k j : Fin 3) : ℝ :=
  if j = k then halfRoot - (s (otherSides k).1 + s (otherSides k).2) else s j

theorem extremeRanges_sound {S : Fin 3 → Interval} {s : Fin 3 → ℝ}
    (hs : ∀ i, (S i).Contains (s i)) (k j : Fin 3) :
    (extremeRanges S k j).Contains (extremeValues s k j) := by
  by_cases h : j = k
  · simpa [extremeRanges, extremeValues, h] using
      sub_contains heightRange_sound (add_contains (hs (otherSides k).1) (hs (otherSides k).2))
  · simpa [extremeRanges, extremeValues, h] using hs j

def coefficientRange (B : Fin 3 → Interval) (i j : Fin 3) : Interval :=
  mul (singleton (4/3)) (add (B i) (mul (singleton (1/2)) (B j)))

noncomputable def coefficientValue (b : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  (4/3) * (b i + (1/2) * b j)

theorem coefficientRange_sound {B : Fin 3 → Interval} {b : Fin 3 → ℝ}
    (hb : ∀ i, (B i).Contains (b i)) (i j : Fin 3) :
    (coefficientRange B i j).Contains (coefficientValue b i j) := by
  simpa [coefficientRange, coefficientValue] using
    mul_contains (singleton_contains (4/3))
      (add_contains (hb i) (mul_contains (singleton_contains (1/2)) (hb j)))

def intersectionRange (N : Fin 3 → IVec) (B : Fin 3 → Interval) (i j : Fin 3) : IVec :=
  addV (scaleV (coefficientRange B i j) (N i)) (scaleV (coefficientRange B j i) (N j))

noncomputable def intersectionValue (n : Fin 3 → RVec) (b : Fin 3 → ℝ)
    (i j : Fin 3) : RVec :=
  (coefficientValue b i j * (n i).1 + coefficientValue b j i * (n j).1,
   coefficientValue b i j * (n i).2 + coefficientValue b j i * (n j).2)

theorem intersectionRange_sound {N : Fin 3 → IVec} {n : Fin 3 → RVec}
    {B : Fin 3 → Interval} {b : Fin 3 → ℝ}
    (hn : ∀ i, ContainsV (N i) (n i)) (hb : ∀ i, (B i).Contains (b i)) (i j : Fin 3) :
    ContainsV (intersectionRange N B i j) (intersectionValue n b i j) :=
  addV_sound (scaleV_sound (coefficientRange_sound hb i j) (hn i))
    (scaleV_sound (coefficientRange_sound hb j i) (hn j))

/-- Frozen serialization: vertex 0=(0,1), 1=(1,2), 2=(2,0). -/
def vertexSides : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (1, 2), (2, 0)]

def vertexRanges (N : Fin 3 → IVec) (B : Fin 3 → Interval) (i : Fin 3) : IVec :=
  intersectionRange N B (vertexSides i).1 (vertexSides i).2

noncomputable def vertexValues (n : Fin 3 → RVec) (b : Fin 3 → ℝ) (i : Fin 3) : RVec :=
  intersectionValue n b (vertexSides i).1 (vertexSides i).2

theorem vertexRanges_sound {N : Fin 3 → IVec} {n : Fin 3 → RVec}
    {B : Fin 3 → Interval} {b : Fin 3 → ℝ}
    (hn : ∀ i, ContainsV (N i) (n i)) (hb : ∀ i, (B i).Contains (b i)) (i : Fin 3) :
    ContainsV (vertexRanges N B i) (vertexValues n b i) :=
  intersectionRange_sound hn hb (vertexSides i).1 (vertexSides i).2

structure SegmentWitness where
  first : Fin 3
  second : Fin 3
  weight : ℚ

def segmentRange (V : Fin 3 → IVec) (w : SegmentWitness) : IVec :=
  addV (scaleV (singleton (1 - w.weight)) (V w.first))
    (scaleV (singleton w.weight) (V w.second))

noncomputable def segmentValue (v : Fin 3 → RVec) (w : SegmentWitness) : RVec :=
  ((1 - (w.weight : ℝ)) * (v w.first).1 + (w.weight : ℝ) * (v w.second).1,
   (1 - (w.weight : ℝ)) * (v w.first).2 + (w.weight : ℝ) * (v w.second).2)

theorem segmentRange_sound {V : Fin 3 → IVec} {v : Fin 3 → RVec}
    (hv : ∀ i, ContainsV (V i) (v i)) (w : SegmentWitness) :
    ContainsV (segmentRange V w) (segmentValue v w) := by
  simpa [segmentRange, segmentValue] using
    addV_sound (scaleV_sound (singleton_contains (1 - w.weight)) (hv w.first))
      (scaleV_sound (singleton_contains w.weight) (hv w.second))

def segmentCheck (V : Fin 3 → IVec) (w : SegmentWitness) : Bool :=
  decide (0 ≤ w.weight ∧ w.weight ≤ 1 ∧ (normSqRange (segmentRange V w)).hi < 1/4)

theorem segmentCheck_sound {V : Fin 3 → IVec} {v : Fin 3 → RVec}
    (hv : ∀ i, ContainsV (V i) (v i)) (w : SegmentWitness) (h : segmentCheck V w = true) :
    0 ≤ (w.weight : ℝ) ∧ (w.weight : ℝ) ≤ 1 ∧
      NI.normSq (segmentValue v w).1 (segmentValue v w).2 < 1/4 := by
  simp only [segmentCheck, decide_eq_true_eq] at h
  have hb := (normSqRange_sound (segmentRange_sound hv w)).2
  have hcast : ((normSqRange (segmentRange V w)).hi : ℝ) < ((1/4 : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).2 h.2.2
  have h' : ((normSqRange (segmentRange V w)).hi : ℝ) < 1/4 := by simpa using hcast
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1, hb.trans_lt h'⟩

inductive LeafKind where
  | support
  | threeExtremes (witnesses : Fin 3 → SegmentWitness)

def extremeCheck (N : Fin 3 → IVec) (w : Fin 3 → SegmentWitness) (k : Fin 3) : Bool :=
  segmentCheck (vertexRanges N (extremeRanges (supportRanges N) k)) (w k)

def leafCheck (C S : Interval) (kind : LeafKind) : Bool :=
  match kind with
  | .support => supportCheck (normalRanges C S)
  | .threeExtremes w =>
      extremeCheck (normalRanges C S) w 0 &&
      extremeCheck (normalRanges C S) w 1 &&
      extremeCheck (normalRanges C S) w 2

def cellCheck (I : Interval) (kind : LeafKind) : Bool :=
  if h : -1 ≤ I.lo ∧ I.hi ≤ 1 then leafCheck (cosRange I) (sinRange I h.1 h.2) kind
  else false

noncomputable def extremeSegmentValue (c s : ℝ) (k : Fin 3) (w : SegmentWitness) : RVec :=
  segmentValue (vertexValues (normalValues c s)
    (extremeValues (supportValues (normalValues c s)) k)) w

def LeafValid (c s : ℝ) : LeafKind → Prop
  | .support => halfRoot < supportValues (normalValues c s) 0 +
      supportValues (normalValues c s) 1 + supportValues (normalValues c s) 2
  | .threeExtremes w => ∀ k, 0 ≤ ((w k).weight : ℝ) ∧ ((w k).weight : ℝ) ≤ 1 ∧
      NI.normSq (extremeSegmentValue c s k (w k)).1 (extremeSegmentValue c s k (w k)).2 < 1/4

theorem leafCheck_sound {C S : Interval} {c s : ℝ} {kind : LeafKind}
    (hc : C.Contains c) (hs : S.Contains s) (h : leafCheck C S kind = true) :
    LeafValid c s kind := by
  have hn := normalRanges_sound hc hs
  have hb := supportRanges_sound hn
  cases kind with
  | support => exact supportCheck_sound hn h
  | threeExtremes w =>
      simp only [leafCheck, Bool.and_eq_true] at h
      have hk : ∀ k, extremeCheck (normalRanges C S) w k = true := by
        intro k
        fin_cases k
        · exact h.1.1
        · exact h.1.2
        · exact h.2
      intro k
      exact segmentCheck_sound
        (vertexRanges_sound hn (extremeRanges_sound hb k)) (w k) (hk k)

theorem cellCheck_sound {I : Interval} {kind : LeafKind} (h : cellCheck I kind = true)
    (t : ℝ) (ht : I.Contains t) : LeafValid (NI.circleX t) (NI.circleY t) kind := by
  by_cases hb : -1 ≤ I.lo ∧ I.hi ≤ 1
  · simp only [cellCheck, dif_pos hb] at h
    exact leafCheck_sound (cosRange_sound ht) (sinRange_sound hb.1 hb.2 ht) h
  · simp [cellCheck, hb] at h

/-- Payloads transcribed from the frozen JSON, in its original cell order. -/
def q25Kinds : List LeafKind := [
  .threeExtremes ![⟨2, 0, 20999476981970417372157704814569344765363784126904833822181935297/21420264003644822451606047013275828628883680456073661395121471488⟩, ⟨0, 1, 0⟩, ⟨2, 0, 177140797661307985327537787703851/187612288833777951421512074395648⟩],
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .support,
  .threeExtremes ![⟨2, 0, 11445650427739063776810705318327353298486589508490140404038999641/187794705412412092054932848762960850993768150692853700838310281216⟩, ⟨2, 0, 1947456709763820590560599376746176/18517987663418581007669818410677527⟩, ⟨2, 0, 357726029975289294795503609730327/21382730324649773544446389668282368⟩],
  .threeExtremes ![⟨2, 0, 106336533933812138229418889109786200196282907655156975882760725/3675666604175738763885061321804727989571755817906131245316702208⟩, ⟨2, 0, 19408826545076159788051443017312/362448710582589471575303536138651⟩, ⟨2, 0, 23452708986137362285252994536671/5440756376179560591223850157473792⟩],
  .threeExtremes ![⟨1, 2, 1⟩, ⟨1, 2, 73251951647046303953194188194345555704119580623469831493763396283855694747063593148273990484883/74855347923494176511209762414618776257375887369742816438054142083580640492578229082356903494547⟩, ⟨1, 2, 371547162674343797695734257316868993366893777014570714693842466985638891041998437566627418385249/374276739617470882556048812073093881286879436848714082190270710417903202462891145411784517472735⟩],
  .support,
  .support,
  .support,
  .support,
  .support,
  .support]

def q25Certificate : List (Interval × LeafKind) := q25Cells.zip q25Kinds

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem q25_all_cells_checked : q25Certificate.all (fun leaf => cellCheck leaf.1 leaf.2) = true := by
  decide +kernel

theorem q25_certificate_partition :
    partitionFrom (-1) 1 (q25Certificate.map Prod.fst) = true := by
  change partitionFrom (-1) 1 q25Cells = true
  exact q25_partition_checked

/-- Actual stored cell checks imply continuous real statements at every chart parameter.
The geometric membership of the constructed extreme points is a separate theorem. -/
theorem q25_continuous_certificate (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    ∃ kind, LeafValid (NI.circleX t) (NI.circleY t) kind := by
  obtain ⟨I, hI, htI⟩ := partitionFrom_sound (q25Certificate.map Prod.fst) (-1) 1
    q25_certificate_partition (by norm_num) t (by simpa using ht)
  obtain ⟨leaf, hleaf, heq⟩ := List.mem_map.mp hI
  subst I
  have hcheck : cellCheck leaf.1 leaf.2 = true :=
    (List.all_eq_true.mp q25_all_cells_checked) leaf hleaf
  exact ⟨leaf.2, cellCheck_sound hcheck t htI⟩

end HexagonCover.NICertificate
