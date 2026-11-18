import HexagonCover.NPacketBounds

/-! Exact necessary reach windows for M in [81/100,83/100]. Stored decimal
approximations are used only after their safe rational inequalities are proved. -/
namespace HexagonCover.SmallestN.ScalarBounds
open HexagonCover.Configuration NormalizedHeavy
noncomputable section

structure Band {config : Fin 7 → UnitTriangle} (h : Normalized config) : Prop where
  lower : (81:ℝ)/100 ≤ M h
  upper : M h ≤ (83:ℝ)/100

def forwardLength : Fin 6 → ℝ :=
  ![7193/10000,6923/10000,6923/10000,6923/10000,6923/10000,81/100]

theorem backward_lower {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (band : Band h) (i : Fin 6) : (17:ℝ)/100 ≤ a h.cover i := by
  have hl := ((structure_bounds h).1 i).trans (min_le_left _ _)
  linarith [band.upper]

theorem a5_upper {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (band : Band h) : a h.cover 5 ≤ (3077:ℝ)/10000 :=
  NPacketBounds.endpoint_upper h (L:=(81:ℝ)/100) (by norm_num) band.lower
    (by norm_num) (by norm_num)

theorem a1_upper {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (band : Band h) :
    a h.cover 1 ≤ (2807:ℝ)/10000 := by
  have hw := NPacketBounds.area_window h nogaps (L:=(81:ℝ)/100) (U:=(83:ℝ)/100)
    (by norm_num) band.lower band.upper (by norm_num) (1:Fin 5)
  norm_num at hw
  apply NPacketBounds.scalar_window_upper (x:=a h.cover 1) (c:=4) (B:=(63:ℝ)/200)
    (by norm_num) (leftReach h.cover 1).positive.le (by norm_num)
  · linarith
  · norm_num

theorem forward_lower {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (band : Band h) (i : Fin 6) :
    forwardLength i ≤ b h.cover i := by
  have ha1 := a1_upper h nogaps band
  have ha5 := a5_upper h band
  have hall (j : Fin 6) : a h.cover j ≤ (3077:ℝ)/10000 :=
    ((NoGapChain.a_strictMono h nogaps).monotone (Fin.le_last j)).trans ha5
  have join (j : Fin 6) : 1 ≤ b h.cover j+a h.cover (j+1) := le_of_not_gt (nogaps j)
  fin_cases i
  · have hj := join 0
    change 1 ≤ b h.cover 0+a h.cover 1 at hj
    change (7193:ℝ)/10000 ≤ b h.cover 0
    linarith
  · have hj := join 1
    change 1 ≤ b h.cover 1+a h.cover 2 at hj
    change (6923:ℝ)/10000 ≤ b h.cover 1
    linarith [hall 2]
  · have hj := join 2
    change 1 ≤ b h.cover 2+a h.cover 3 at hj
    change (6923:ℝ)/10000 ≤ b h.cover 2
    linarith [hall 3]
  · have hj := join 3
    change 1 ≤ b h.cover 3+a h.cover 4 at hj
    change (6923:ℝ)/10000 ≤ b h.cover 3
    linarith [hall 4]
  · have hj := join 4
    change 1 ≤ b h.cover 4+a h.cover 5 at hj
    change (6923:ℝ)/10000 ≤ b h.cover 4
    linarith
  · exact band.lower

theorem forward_bounds (i : Fin 6) : forwardLength i ∈ Set.Icc (0:ℝ) 1 := by
  fin_cases i <;> norm_num [forwardLength]

end
end HexagonCover.SmallestN.ScalarBounds
