import HexagonCover.E4InsideRegion

/-! Actual moving-point duties for the E4 owner-transfer chain. The lower
point's T4 interior conclusion explicitly waits for the missing T3 exclusion;
the upper Qt union duty is unconditional within the sole-E4 family. -/
namespace HexagonCover.E4InsideOwners
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

theorem Pa_interior_hexagon {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    E4InsideCentral.Pa a∈interior (Hexagon 1) := by
  have hb : point 0 (-h₀)∈Hexagon 1 := by
    simpa using E4InsideRegion.center_box_mem_hexagon
      (x:=0) (Y:=-1) (by norm_num) (by norm_num)
  have hm := (convex_hexagon 1).combo_interior_self_mem_interior
    (zero_mem_interior_hexagon (by norm_num)) hb
    (a:=1-a) (b:=a) (by linarith) ha.le (by ring)
  have he : (1-a) • (0:Plane)+a • point 0 (-h₀)=E4InsideCentral.Pa a := by
    ext i
    fin_cases i <;> simp [E4InsideCentral.Pa] <;> ring
  exact he ▸ hm

theorem Pa_anchor_far {a : ℝ} (ha : 0 < a) (i : Fin 6) (hi3 : i≠3) (hi4 : i≠4) :
    1 < (dist (E4InsideCentral.Pa a) (vertex i))^2 := by
  fin_cases i
  all_goals try exact (hi3 rfl).elim
  all_goals try exact (hi4 rfl).elim
  all_goals norm_num [E4InsideCentral.Pa,vertex_table,dist_point_sq]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals nlinarith [sq_pos_of_pos ha]

/-- Conditional on the still-required exclusion of closed T3, actual Pa
lies in the interior of actual T4. Closed shared T3/T4 ownership is not skipped. -/
theorem actual_Pa_interior_four_of_not_three {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (hthree : E4InsideCentral.Pa (a h.cover 5)∉(rotateConfig config 3).region) :
    E4InsideCentral.Pa (a h.cover 5)∈interior (rotateConfig config 4).region := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  let others : Set Plane := ⋃i:{j:Fin 7 // j≠4},(rotateConfig config i.val).region
  have hclosed : IsClosed others := isClosed_iUnion_of_finite
    (fun i:{j:Fin 7 // j≠4}=>(rotateConfig config i.val).closed_region)
  have hopen : IsOpen (interior (Hexagon 1) \ others) := isOpen_interior.sdiff hclosed
  have outer (i:Fin 6) (hi3:i≠3) (hi4:i≠4) :
      E4InsideCentral.Pa (a h.cover 5)∉(rotateConfig config i.castSucc).region := by
    intro hp
    have hd := (rotateConfig config i.castSucc).dist_le_one hp (anchors h.cover i)
    have hf := Pa_anchor_far ha i hi3 hi4
    nlinarith [dist_nonneg (x:=E4InsideCentral.Pa (a h.cover 5)) (y:=vertex i)]
  have hp : E4InsideCentral.Pa (a h.cover 5)∈interior (Hexagon 1) \ others := by
    refine ⟨Pa_interior_hexagon ha (by linarith),?_⟩
    intro hm
    obtain ⟨⟨i,hi⟩,hpi⟩ := Set.mem_iUnion.mp hm
    fin_cases i
    · exact outer 0 (by decide) (by decide) hpi
    · exact outer 1 (by decide) (by decide) hpi
    · exact outer 2 (by decide) (by decide) hpi
    · exact hthree hpi
    · exact hi rfl
    · exact outer 5 (by decide) (by decide) hpi
    · exact E4InsideCentral.actual_excluded h sole hpi
  have hsubset : interior (Hexagon 1) \ others ⊆ (rotateConfig config 4).region := by
    intro p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (covered h.cover (interior_subset hp.1))
    by_cases he : i=4
    · simpa only [he] using hi
    · exact (hp.2 (Set.mem_iUnion.mpr ⟨⟨i,he⟩,hi⟩)).elim
  apply interior_mono hsubset
  rwa [hopen.interior_eq]

def Qt (t : ℝ) : Plane := point (-t) (2*h₀*t/3)

theorem Qt_anchor_far {t : ℝ} (ht : 0 < t) (i : Fin 6) (hi1:i≠1) (hi2:i≠2) :
    1 < (dist (Qt t) (vertex i))^2 := by
  fin_cases i
  all_goals try exact (hi1 rfl).elim
  all_goals try exact (hi2 rfl).elim
  all_goals norm_num [Qt,vertex_table,dist_point_sq]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals nlinarith [sq_pos_of_pos ht]

theorem Qt_P_far {a t : ℝ} (ha : a < 2*t) :
    1 < (dist (Qt t) (CentralAxis.P a))^2 := by
  have he : CentralAxis.P a=point (1-a/2) (-h₀*a) := by
    ext i
    fin_cases i <;> simp [CentralAxis.P,ExteriorLoss.lowerEndpoint,
      ExteriorLoss.corner,ExteriorLoss.lowerRay] <;> ring
  rw [he,Qt,dist_point_sq]
  have hh : 0 < t-a/2 := by linarith
  nlinarith [sq_nonneg (t-a/2),sq_nonneg (2*h₀*t/3-(-h₀*a))]

/-- The moving upper duty belongs to the same T1 union T2, including shared
ownership. No T1-only corridor premise is introduced. -/
theorem actual_Qt_union {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    Qt (1-M h)∈(rotateConfig config 1).region ∨
      Qt (1-M h)∈(rotateConfig config 2).region := by
  have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩
  have hM1 := (structure_bounds h).2.2.2.2.1
  have ht : 0 < 1-M h := by linarith
  have hex : Qt (1-M h)∈Hexagon 1 := by
    have hh := E4InsideRegion.center_box_mem_hexagon (x:=-(1-M h)) (Y:=2*(1-M h)/3)
      (by constructor <;> linarith) (by constructor <;> linarith)
    have he : point (-(1-M h)) (h₀*(2*(1-M h)/3))=Qt (1-M h) := by
      ext i
      fin_cases i <;> simp [Qt] <;> ring
    exact he ▸ hh
  have hc : Qt (1-M h)∉(rotateConfig config 6).region := by
    intro hp
    have hd := (rotateConfig config 6).dist_le_one hp (CentralAxis.source_P_mem h ((sole 4).mpr rfl))
    have hf := Qt_P_far (GapChains.heavy_short h)
    nlinarith [dist_nonneg (x:=Qt (1-M h)) (y:=CentralAxis.P (a h.cover 5))]
  have outer (i:Fin 6) (hi1:i≠1) (hi2:i≠2) : Qt (1-M h)∉(rotateConfig config i.castSucc).region := by
    intro hp
    have hd := (rotateConfig config i.castSucc).dist_le_one hp (anchors h.cover i)
    have hf := Qt_anchor_far ht i hi1 hi2
    nlinarith [dist_nonneg (x:=Qt (1-M h)) (y:=vertex i)]
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (covered h.cover hex)
  fin_cases i
  · exact (outer 0 (by decide) (by decide) hi).elim
  · exact Or.inl hi
  · exact Or.inr hi
  · exact (outer 3 (by decide) (by decide) hi).elim
  · exact (outer 4 (by decide) (by decide) hi).elim
  · exact (outer 5 (by decide) (by decide) hi).elim
  · exact (hc hi).elim

#print axioms actual_Pa_interior_four_of_not_three
#print axioms actual_Qt_union

end
end HexagonCover.E4InsideOwners
