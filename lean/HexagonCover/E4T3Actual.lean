import HexagonCover.E4T3Frame
import HexagonCover.E4InsideArea
import HexagonCover.E4InsideRegion
import HexagonCover.E4InsideSeamAlgebra

/-! Same-configuration T3 data extracted from actual active finite sides.
The sole-E4 and closed-Pa hypotheses supply all orientation and reach bounds;
no T3 chart condition is left as a new assumption on the covering problem. -/
namespace HexagonCover.E4T3Actual
noncomputable section
open TriangleFrame SupportGeometry SourceCoordinates E4T3Frame
open HexagonCover.Configuration NormalizedHeavy
local notation "h₀" => NICertificate.halfRoot

theorem actual_window {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (hPa : E4InsideCentral.Pa (a h.cover 5)∈(rotateConfig config 3).region)
    (f : Frame (rotateConfig config 3) (b h.cover 3)) :
    -f.c/2<h₀*f.d ∧ h₀*f.d<f.c/2 := by
  have ha := E4InsideCentral.actual_a_bounds h sole
  have hshort := GapChains.heavy_short h
  have ha3 := ((structure_bounds h).1 3).trans (min_le_left _ _)
  have hb := (SoleGapArea.light_reach_order h sole (3:Fin 5)).2
  have hlight := NoGapChain.light h (3:Fin 5)
  change 1/2 < b h.cover 3 at hb
  change a h.cover 3+b h.cover 3 < 1 at hlight
  have hleft := left_endpoint h.cover 3
    ⟨(leftReach h.cover 3).positive.le,(leftReach h.cover 3).lt_one.le⟩ le_rfl
  apply window f (by linarith [ha.2]) (by linarith) (by linarith [ha.2]) hlight hPa
  exact hleft

/-- The backward maximum must use row1. Other rows have negative ray
projection, so this also rules out every possible tied backward side. -/
theorem actual_backward_margin {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (hPa : E4InsideCentral.Pa (a h.cover 5)∈(rotateConfig config 3).region)
    (f : Frame (rotateConfig config 3) (b h.cover 3)) : f.margin 1=f.c*a h.cover 3 := by
  have hw := actual_window h sole hPa f
  obtain ⟨i,hproj,hactive⟩ := E4InsideSourceActive.left_active h.cover 3 f.unit f.absolute_mem
  have hi : i=1 := backward_positive_unique hw.1 hw.2 i hproj
  subst i
  change dotp (nvec f.c f.d 1) (leftPoint (a h.cover 3))=
    f.margin 1+dotp (nvec f.c f.d 1) anchor at hactive
  have he : dotp (nvec f.c f.d 1) (leftPoint (a h.cover 3)-anchor)=f.margin 1 := by
    rw [dotp_sub_right]
    linarith only [hactive]
  rw [left_dot] at he
  norm_num at he
  nlinarith only [he]

/-- Every active side at either genuine actual maximum has the displayed
unique index. Forward and backward indices are distinct. -/
theorem actual_exit_uniqueness {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (hPa : E4InsideCentral.Pa (a h.cover 5)∈(rotateConfig config 3).region)
    (f : Frame (rotateConfig config 3) (b h.cover 3)) :
    (∀i,dotp (nvec f.c f.d i) (rightPoint (b h.cover 3)-anchor)=f.margin i → i=0) ∧
    (∀i,dotp (nvec f.c f.d i) (leftPoint (a h.cover 3)-anchor)=f.margin i → i=1) := by
  have hw := actual_window h sole hPa f
  exact ⟨f.forward_active_unique (rightReach h.cover 3).positive hw.1 hw.2,
    f.backward_active_unique (leftReach h.cover 3).positive hw.1 hw.2⟩

structure Data (T : UnitTriangle) (a a3 b3 : ℝ) where
  δ : ℝ
  S : ℝ
  δpos : 0<δ
  δhalf : δ<1/2
  Spos : 0<S
  square : S^2=1-δ+δ^2
  budget : a3+b3<S
  Pa_forward : 1-a/2-(1-a)*δ≤b3
  Pa_backward : -a/2+(1-a/2)*δ≤a3
  upper_cap : ∀Y:ℝ,point (-1/4) (h₀*Y)∈T.region →
    Y≤2*(a3+1/4-δ/4)/(1+δ)-1

theorem actual_data {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (hPa : E4InsideCentral.Pa (a h.cover 5)∈(rotateConfig config 3).region) :
    Nonempty (Data (rotateConfig config 3) (a h.cover 5) (a h.cover 3) (b h.cover 3)) := by
  obtain ⟨f⟩ := actual_frame h.cover
  have hw := actual_window h sole hPa f
  have hback := actual_backward_margin h sole hPa f
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  have ha3 := E4InsideArea.a3_lt_third h sole
  have hp0 := (f.mem _).mp hPa 0
  change dotp (nvec f.c f.d 0) (point 0 (-h₀*a h.cover 5)-anchor)≤f.margin 0 at hp0
  rw [Pa_dot_zero,f.forward] at hp0
  have hp1 := (f.mem _).mp hPa 1
  change dotp (nvec f.c f.d 1) (point 0 (-h₀*a h.cover 5)-anchor)≤f.margin 1 at hp1
  rw [Pa_dot_one,hback] at hp1
  have hd := E4T3Scalar.positive_direction f.c_pos ha ha1 ha3 hp1
  have hδ := E4T3Scalar.delta_bounds f.c_pos hd hw.2
  have hs := E4T3Scalar.scale_identity f.c_pos f.unit
  have hSpos : 0<E4T3Scalar.scale f.c := div_pos ExtremeTriangle.halfRoot_pos f.c_pos
  have hbudget : a h.cover 3+b h.cover 3<E4T3Scalar.scale f.c := by
    have hsum := f.sum
    rw [f.forward,hback] at hsum
    apply (lt_div_iff₀ f.c_pos).mpr
    nlinarith only [hsum,f.positive 2]
  have hrows := E4T3Scalar.Pa_rows f.c_pos hp0 hp1
  refine ⟨⟨E4T3Scalar.delta f.c f.d,E4T3Scalar.scale f.c,hδ.1,hδ.2,hSpos,hs,
    hbudget,hrows.1,hrows.2,?_⟩⟩
  intro Y hY
  have hm := (f.mem _).mp hY 1
  rw [hback] at hm
  have he : dotp (nvec f.c f.d 1) (point (-1/4) (h₀*Y)-anchor)=
      f.c*(-1/8+(3/4)*(Y+1))-h₀*f.d*(1/4+(Y+1)/2) := by
    simp [anchor,vertex_table,nvec,NICertificate.normalValues,dotp]
    ring_nf
    rw [ExtremeTriangle.halfRoot_sq]
    ring
  rw [he] at hm
  have hquot : f.c*(h₀*f.d/f.c)=h₀*f.d := by field_simp [ne_of_gt f.c_pos]
  have hmul : (1+E4T3Scalar.delta f.c f.d)*(Y+1)≤
      2*(a h.cover 3+1/4-E4T3Scalar.delta f.c f.d/4) := by
    apply (mul_le_mul_iff_of_pos_left f.c_pos).mp
    unfold E4T3Scalar.delta
    nlinarith only [hm,hquot,congrArg (fun z : ℝ => z*Y) hquot]
  have hdiv : Y+1≤2*(a h.cover 3+1/4-E4T3Scalar.delta f.c f.d/4)/
      (1+E4T3Scalar.delta f.c f.d) := by
    apply (le_div_iff₀ (by linarith [hδ.1] : 0<1+E4T3Scalar.delta f.c f.d)).mpr
    nlinarith only [hmul]
  linarith only [hdiv]

theorem Data.height_cap {T : UnitTriangle} {a a3 b3 : ℝ} (w : Data T a a3 b3) :
    2*(a3+1/4-w.δ/4)/(1+w.δ)-1<a-1/2 :=
  E4InsideSeamAlgebra.t3_height_cap w.δpos w.δhalf w.Spos.le w.square
    w.budget w.Pa_forward w.Pa_backward

theorem Data.moving_point_excluded {T : UnitTriangle} {a a3 b3 : ℝ} (w : Data T a a3 b3) :
    point (-1/4) (h₀*(a-1/2))∉T.region := by
  intro hp
  have hu := w.upper_cap (a-1/2) hp
  have hc := w.height_cap
  linarith only [hu,hc]

/-- The moving lower point is assigned by the actual whole-rectangle duty,
after excluding the same T3 by its real finite supporting side. -/
theorem actual_lower_duty {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (hPa : E4InsideCentral.Pa (a h.cover 5)∈(rotateConfig config 3).region) :
    point (-1/4) (h₀*(a h.cover 5-1/2))∈(rotateConfig config 2).region := by
  obtain ⟨w⟩ := actual_data h sole hPa
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  have hrect := E4InsideRegion.actual_lower_rectangle h sole
    (x:=-1/4) (Y:=a h.cover 5-1/2) ⟨by norm_num,le_rfl⟩
    ⟨by linarith,by linarith⟩
  exact hrect.resolve_right w.moving_point_excluded

end
end HexagonCover.E4T3Actual

#print axioms HexagonCover.E4T3Actual.actual_data
#print axioms HexagonCover.E4T3Actual.actual_exit_uniqueness
#print axioms HexagonCover.E4T3Actual.actual_lower_duty
