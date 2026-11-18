import HexagonCover.E4InsideRayChart

/-! Each source role uses the same actual triangle and its actual finite
backward/forward reaches. Cyclic relabelling of support rows is harmless;
there is no replacement placement or unproved direction restriction. -/
namespace HexagonCover.E4InsideActualChart
noncomputable section
open TriangleFrame SupportGeometry
open HexagonCover.Configuration SourceCoordinates
open E4InsideRayChart
local notation "h₀" => NICertificate.halfRoot

def back (i : Fin 6) : Plane := vertex (i-1)-vertex i
def forward (i : Fin 6) : Plane := vertex (i+1)-vertex i

theorem back_unit (i : Fin 6) : (back i 0)^2+(back i 1)^2=1 := by
  fin_cases i <;> norm_num [back,vertex_table,ExtremeTriangle.halfRoot_sq]

theorem back_eta (i : Fin 6) : point (back i 0) (back i 1)=back i := by
  ext j
  fin_cases j <;> simp

theorem forward_eq (i : Fin 6) : forward i=nvec (back i 0) (back i 1) 2 := by
  fin_cases i <;> ext j <;> fin_cases j
  all_goals norm_num [forward,back,vertex_table,nvec,NICertificate.normalValues]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem line_eq (U V : Plane) (t : ℝ) : U+t • (V-U)=AffineMap.lineMap U V t := by
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply] <;> ring

theorem exists_chart {config : Fin 7→UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    Nonempty (Chart (rotateConfig config i.castSucc) (vertex i) (back i) (forward i)
      (a h i)) := by
  obtain ⟨c,d,offs,_,hu,hsum,hmem⟩ := exists_normal_frame (rotateConfig config i.castSucc)
  obtain ⟨k,hproj,hactive⟩ := E4InsideSourceActive.left_active h i hu hmem
  let c' : ℝ := nvec c d k 0
  let d' : ℝ := nvec c d k 1
  let offs' : Fin 3→ℝ := fun j=>offs (k+j)
  have hunit : c'^2+d'^2=1 := by
    have hg := nvec_gram hu k k
    simp only [ite_true] at hg
    change c'*c'+d'*d'=1 at hg
    nlinarith
  have hsum' : offs' 0+offs' 1+offs' 2=h₀ := by
    dsimp only [offs']
    fin_cases k <;> norm_num <;> linarith
  have hmem' : ∀z:Plane,z∈(rotateConfig config i.castSucc).region ↔
      ∀j,dotp (nvec c' d' j) z≤offs' j := by
    intro z
    rw [hmem]
    change (∀j,dotp (nvec c d j) z≤offs j) ↔ _
    dsimp only [c',d',offs']
    simp_rw [CornerChart.nvec_cyclic]
    constructor
    · intro hz j; exact hz (k+j)
    · intro hz j
      have hj : k+(j-k)=j := by abel
      simpa only [hj] using hz (j-k)
  have he0 : nvec c' d' 0=nvec c d k := by
    dsimp only [c',d']
    rw [CornerChart.nvec_cyclic,add_zero]
  obtain ⟨ε,hε,hball⟩ := E4InsideSourceActive.source_anchor_ball h i
  have hp : 0 < dotp (nvec c' d' 0) (point (back i 0) (back i 1)) := by
    rw [back_eta,he0]
    exact hproj
  have ha : dotp (nvec c' d' 0) (vertex i+a h i • point (back i 0) (back i 1))=
      offs' 0 := by
    rw [back_eta,he0]
    change dotp (nvec c d k) (vertex i+a h i • (vertex (i-1)-vertex i))=offs (k+0)
    rw [add_zero,line_eq]
    exact hactive
  have hh := of_active (rotateConfig config i.castSucc) (vertex i) hunit (back_unit i)
    hsum' hmem' hε hball hp ha
  simpa only [back_eta,←forward_eq] using hh

theorem forward_character {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (i : Fin 6) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    vertex i+t • forward i∈(rotateConfig config i.castSucc).region ↔ t≤b h i := by
  have hh := (ReachEquiv.mapReach Symmetry.turn (rightReach h i)).character t ht
  simpa only [ReachEquiv.mapReach,turn_vertex_eq,forward,line_eq,b,rotateConfig] using hh

theorem forward_active {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (i : Fin 6)
    (ch : Chart (rotateConfig config i.castSucc) (vertex i) (back i) (forward i) (a h i)) :
    -(1+ch.r)*b h i=a h i ∨ ch.r*b h i=ch.d ∨ b h i=ch.e :=
  ch.forward_exit_active (rightReach h i).positive (rightReach h i).lt_one
    (forward_character h i)

theorem forward_tests {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (i : Fin 6)
    (ch : Chart (rotateConfig config i.castSucc) (vertex i) (back i) (forward i) (a h i)) :
    -(1+ch.r)*b h i≤a h i ∧ ch.r*b h i≤ch.d ∧ b h i≤ch.e := by
  have hm := (forward_character h i (b h i)
    ⟨(rightReach h i).positive.le,(rightReach h i).lt_one.le⟩).mpr le_rfl
  have hh := (ch.character 0 (b h i)).mp (by simpa using hm)
  exact ⟨by have h0 := hh 0; simp only [rows,Matrix.cons_val_zero] at h0; nlinarith only [h0],
    by simpa [rows] using hh 1,by simpa [rows] using hh 2⟩

#print axioms exists_chart
#print axioms forward_active

end
end HexagonCover.E4InsideActualChart
