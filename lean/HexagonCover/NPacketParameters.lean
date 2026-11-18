import HexagonCover.NPacketBounds

/-! Computable rational guards for N packets, with necessary bounds on one
actual normalized no-gap configuration. Source point identities are separate. -/
namespace HexagonCover.NPacketParameters
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates

structure Parameters where
  lower : ℚ
  upper : ℚ
  endpoint : ℚ
  lightUpper : Fin 5 → ℚ
  centralRadius : ℚ
  radiusSquared : ℚ

def check (p : Parameters) : Bool := decide (
  0 < p.lower ∧ p.lower ≤ p.upper ∧ p.upper < 1 ∧
  0 ≤ p.endpoint ∧ p.endpoint ≤ 1 ∧
  1 ≤ p.endpoint^2+p.lower*p.endpoint+p.lower^2 ∧
  (∀ j : Fin 5, 0 ≤ p.lightUpper j ∧ p.lightUpper j ≤ 1 ∧
    (p.endpoint ≤ p.lightUpper j ∨
      1 ≤ p.lower^2+(j.val:ℚ)*(1-p.upper)^2+(5-(j.val:ℚ))*(p.lightUpper j)^2)) ∧
  0 ≤ p.centralRadius ∧ p.centralRadius ≤ (1-p.upper)*p.upper/2 ∧
  0 < p.radiusSquared ∧ p.radiusSquared ≤ 3*p.lower^2/4)

structure Guards (p : Parameters) : Prop where
  lower_pos : 0 < (p.lower:ℝ)
  lower_upper : (p.lower:ℝ) ≤ p.upper
  upper_one : (p.upper:ℝ) < 1
  endpoint_nonneg : 0 ≤ (p.endpoint:ℝ)
  endpoint_one : (p.endpoint:ℝ) ≤ 1
  endpoint_exit : 1 ≤ (p.endpoint:ℝ)^2+(p.lower:ℝ)*p.endpoint+(p.lower:ℝ)^2
  light : ∀ j : Fin 5, 0 ≤ (p.lightUpper j:ℝ) ∧ (p.lightUpper j:ℝ) ≤ 1 ∧
    ((p.endpoint:ℝ) ≤ p.lightUpper j ∨
      1 ≤ (p.lower:ℝ)^2+(j.val:ℝ)*(1-(p.upper:ℝ))^2+
        (5-(j.val:ℝ))*(p.lightUpper j:ℝ)^2)
  central_nonneg : 0 ≤ (p.centralRadius:ℝ)
  central_safe : (p.centralRadius:ℝ) ≤ (1-(p.upper:ℝ))*(p.upper:ℝ)/2
  radius_pos : 0 < (p.radiusSquared:ℝ)
  radius_safe : (p.radiusSquared:ℝ) ≤ 3*(p.lower:ℝ)^2/4

theorem guards_of_check {p : Parameters} (accepted : check p = true) : Guards p := by
  have h := of_decide_eq_true accepted
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · intro j
    rcases h6 j with ⟨ha,hb,hc⟩
    refine ⟨?_,?_,?_⟩
    · exact_mod_cast ha
    · exact_mod_cast hb
    · rcases hc with hc | hc
      · left; exact_mod_cast hc
      · right; exact_mod_cast hc
  · exact_mod_cast h7
  · exact_mod_cast h8
  · exact_mod_cast h9
  · exact_mod_cast h10

noncomputable section

structure Band (p : Parameters) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) : Prop where
  lower : (p.lower:ℝ) ≤ M h
  upper : M h ≤ (p.upper:ℝ)

theorem backward_lower (p : Parameters) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (band : Band p h) (i : Fin 6) :
    1-(p.upper:ℝ) ≤ a h.cover i := by
  have hl := ((structure_bounds h).1 i).trans (min_le_left _ _)
  linarith [band.upper]

theorem a5_upper {p : Parameters} (g : Guards p) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (band : Band p h) : a h.cover 5 ≤ (p.endpoint:ℝ) :=
  NPacketBounds.endpoint_upper h g.lower_pos.le band.lower
    g.endpoint_nonneg g.endpoint_exit

theorem light_upper {p : Parameters} (g : Guards p) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i)
    (band : Band p h) (j : Fin 5) : a h.cover j.castSucc ≤ (p.lightUpper j:ℝ) := by
  rcases (g.light j).2.2 with he | hw
  · exact ((NoGapChain.a_strictMono h nogaps).monotone
      (Fin.le_last j.castSucc)).trans ((a5_upper g h band).trans he)
  · have bound := NPacketBounds.area_window h nogaps g.lower_pos.le
      band.lower band.upper g.upper_one.le j
    have hj : (j.val:ℝ) < 5 := by exact_mod_cast j.isLt
    apply NPacketBounds.scalar_window_upper (x:=a h.cover j.castSucc)
      (c:=5-(j.val:ℝ)) (B:=1-(p.lower:ℝ)^2-(j.val:ℝ)*(1-(p.upper:ℝ))^2)
      (by linarith) (leftReach h.cover j.castSucc).positive.le (g.light j).1
    · linarith
    · linarith

def forwardLength (p : Parameters) : Fin 6 → ℝ :=
  ![1-(p.lightUpper 1:ℝ),1-(p.lightUpper 2:ℝ),1-(p.lightUpper 3:ℝ),
    1-(p.lightUpper 4:ℝ),1-(p.endpoint:ℝ),(p.lower:ℝ)]

theorem forward_bounds {p : Parameters} (g : Guards p) (i : Fin 6) :
    forwardLength p i ∈ Set.Icc (0:ℝ) 1 := by
  have h1 := g.light 1
  have h2 := g.light 2
  have h3 := g.light 3
  have h4 := g.light 4
  have light_bound (j : Fin 5) : 1-(p.lightUpper j:ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (g.light j).2.1, sub_le_self _ (g.light j).1⟩
  fin_cases i
  · exact light_bound 1
  · exact light_bound 2
  · exact light_bound 3
  · exact light_bound 4
  · exact ⟨sub_nonneg.mpr g.endpoint_one, sub_le_self _ g.endpoint_nonneg⟩
  · exact ⟨g.lower_pos.le, g.lower_upper.trans g.upper_one.le⟩

theorem forward_lower {p : Parameters} (g : Guards p) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i)
    (band : Band p h) (i : Fin 6) : forwardLength p i ≤ b h.cover i := by
  have join (j : Fin 6) : 1 ≤ b h.cover j+a h.cover (j+1) := le_of_not_gt (nogaps j)
  have h1 := light_upper g h nogaps band 1
  have h2 := light_upper g h nogaps band 2
  have h3 := light_upper g h nogaps band 3
  have h4 := light_upper g h nogaps band 4
  have h5 := a5_upper g h band
  fin_cases i
  · have hj := join 0
    change 1 ≤ b h.cover 0+a h.cover 1 at hj
    change a h.cover 1 ≤ _ at h1
    change 1-(p.lightUpper 1:ℝ) ≤ b h.cover 0
    linarith
  · have hj := join 1
    change 1 ≤ b h.cover 1+a h.cover 2 at hj
    change a h.cover 2 ≤ _ at h2
    change 1-(p.lightUpper 2:ℝ) ≤ b h.cover 1
    linarith
  · have hj := join 2
    change 1 ≤ b h.cover 2+a h.cover 3 at hj
    change a h.cover 3 ≤ _ at h3
    change 1-(p.lightUpper 3:ℝ) ≤ b h.cover 2
    linarith
  · have hj := join 3
    change 1 ≤ b h.cover 3+a h.cover 4 at hj
    change a h.cover 4 ≤ _ at h4
    change 1-(p.lightUpper 4:ℝ) ≤ b h.cover 3
    linarith
  · have hj := join 4
    change 1 ≤ b h.cover 4+a h.cover 5 at hj
    change 1-(p.endpoint:ℝ) ≤ b h.cover 4
    linarith
  · exact band.lower

theorem central_disk {p : Parameters} (g : Guards p) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (band : Band p h) :
    Metric.closedBall (0:Plane) (p.centralRadius:ℝ) ⊆ (rotateConfig config 6).region :=
  (Metric.closedBall_subset_closedBall g.central_safe).trans
    (NPacketBounds.central_safe_radius h (g.lower_pos.trans_le g.lower_upper)
      g.upper_one band.upper)

theorem heavy_radius_sq {p : Parameters} (g : Guards p) {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (band : Band p h) :
    ∀ q ∈ (rotateConfig config 5).region, (p.radiusSquared:ℝ) ≤ ‖q‖^2 := by
  intro q hq
  exact g.radius_safe.trans (NPacketBounds.heavy_radius_sq h g.lower_pos.le band.lower q hq)

end
end HexagonCover.NPacketParameters
