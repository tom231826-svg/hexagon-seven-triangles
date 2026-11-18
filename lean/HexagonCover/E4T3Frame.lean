import HexagonCover.E4InsideSourceActive
import HexagonCover.E4T3Scalar

/-! Source-exposed actual T3 frame selected by a genuine E3-active side.
Only a cyclic relabelling of the three actual normals is performed. No
orientation window, uniqueness of an exit, or endpoint side is assumed. -/
namespace HexagonCover.E4T3Frame
noncomputable section
open TriangleFrame SupportGeometry CornerChart SourceCoordinates
open HexagonCover.Configuration
local notation "h₀" => NICertificate.halfRoot

def anchor : Plane := vertex 3
def leftPoint (a : ℝ) : Plane := AffineMap.lineMap (vertex 3) (vertex 2) a
def rightPoint (b : ℝ) : Plane := AffineMap.lineMap (vertex 3) (vertex 4) b

theorem forward_vector : vertex 4-vertex 3=point 1 0 := by
  ext i
  fin_cases i <;> norm_num [vertex_table]

theorem backward_vector : vertex 2-vertex 3=point (-1/2) h₀ := by
  ext i
  fin_cases i <;> simp [vertex_table] <;> ring

structure Frame (T : UnitTriangle) (b : ℝ) where
  c : ℝ
  d : ℝ
  margin : Fin 3→ℝ
  c_pos : 0<c
  unit : c^2+d^2=1
  positive : ∀i,0 < margin i
  sum : margin 0+margin 1+margin 2=h₀
  mem : ∀p:Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) (p-anchor)≤ margin i
  forward : margin 0=c*b

theorem Frame.absolute_mem {T : UnitTriangle} {b : ℝ} (f : Frame T b) (p : Plane) :
    p∈T.region ↔ ∀i,dotp (nvec f.c f.d i) p≤f.margin i+dotp (nvec f.c f.d i) anchor := by
  rw [f.mem]
  constructor <;> intro hp i <;> have hi := hp i
  · rw [dotp_sub_right] at hi
    linarith only [hi]
  · rw [dotp_sub_right]
    linarith only [hi]

theorem actual_frame {config : Fin 7→UnitTriangle} (h : StrictCover config) :
    Nonempty (Frame (rotateConfig config 3) (b h 3)) := by
  obtain ⟨c,d,offs,_,hu,hsum,hmem⟩ := exists_normal_frame (rotateConfig config 3)
  obtain ⟨j,hjpos,hjactive⟩ := E4InsideSourceActive.right_active h 3 hu hmem
  let c' := (nvec c d j) 0
  let d' := (nvec c d j) 1
  let off' : Fin 3→ℝ := fun i=>offs (j+i)
  have hc' : 0<c' := by
    change 0 < dotp (nvec c d j) (vertex 4-vertex 3) at hjpos
    rw [forward_vector] at hjpos
    simpa [dotp,c'] using hjpos
  have hu' : c'^2+d'^2=1 := by
    have hh := nvec_gram hu j j
    simp only [ite_true] at hh
    change (nvec c d j) 0*(nvec c d j) 0+(nvec c d j) 1*(nvec c d j) 1=1 at hh
    dsimp [c',d']
    nlinarith only [hh]
  have hn (i : Fin 3) : nvec c' d' i=nvec c d (j+i) := nvec_cyclic c d j i
  have hsum' : off' 0+off' 1+off' 2=h₀ := by
    fin_cases j <;> norm_num [off'] <;> linarith only [hsum]
  have hmem' : ∀p:Plane,p∈(rotateConfig config 3).region ↔
      ∀i,dotp (nvec c' d' i) p≤off' i := by
    intro p
    rw [hmem]
    change (∀ i, dotp (nvec c d i) p ≤ offs i) ↔ _
    simp_rw [hn]
    constructor
    · intro hp i
      exact hp (j+i)
    · intro hp i
      simpa [off'] using hp (i-j)
  let margin : Fin 3→ℝ := fun i=>off' i-dotp (nvec c' d' i) anchor
  obtain ⟨ε,hε,hball⟩ := E4InsideSourceActive.source_anchor_ball h 3
  have hpos (i : Fin 3) : 0 < margin i :=
    E4InsideActive.anchor_margin_pos _ hε hball hu' hmem' i
  have hmargins : margin 0+margin 1+margin 2=h₀ := by
    have hns := dot_nvec_sum c' d' anchor
    rw [Fin.sum_univ_three] at hns
    dsimp [margin]
    linarith only [hsum',hns]
  have hmemRel : ∀p:Plane,p∈(rotateConfig config 3).region ↔
      ∀i,dotp (nvec c' d' i) (p-anchor)≤ margin i := by
    intro p
    rw [hmem']
    constructor <;> intro hp i <;> have hi := hp i
    · rw [dotp_sub_right]
      dsimp [margin]
      linarith only [hi]
    · rw [dotp_sub_right] at hi
      dsimp [margin] at hi
      linarith only [hi]
  have hnormal0 : nvec c' d' 0=nvec c d j := by simpa using hn 0
  have hline : AffineMap.lineMap (vertex 3) (vertex ((3:Fin 6)+1)) (b h 3)=
      anchor+(b h 3) • point 1 0 := by
    ext i
    fin_cases i <;> simp [anchor,vertex_table,AffineMap.lineMap_apply] <;> ring
  have hactive : dotp (nvec c' d' 0) (anchor+(b h 3) • point 1 0)=off' 0 := by
    rw [hnormal0]
    simpa only [hline,off',add_zero] using hjactive
  have hf : margin 0=c'*b h 3 := by
    rw [dotp_add_right,dotp_smul_right] at hactive
    have hn0 : dotp (nvec c' d' 0) (point 1 0)=c' := by simp [nvec,NICertificate.normalValues,dotp]
    rw [hn0] at hactive
    dsimp [margin]
    nlinarith only [hactive]
  exact ⟨⟨c',d',margin,hc',hu',hpos,hmargins,hmemRel,hf⟩⟩

theorem left_dot (c d a : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (leftPoint a-anchor)=a* ![-c/2+h₀*d,c,-c/2-h₀*d] i := by
  fin_cases i
  all_goals simp [leftPoint,anchor,vertex_table,AffineMap.lineMap_apply,nvec,NICertificate.normalValues,dotp]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem backward_projection (c d : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (vertex 2-vertex 3)= ![-c/2+h₀*d,c,-c/2-h₀*d] i := by
  rw [backward_vector]
  fin_cases i
  all_goals simp [nvec,NICertificate.normalValues,dotp]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem forward_projection (c d : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (vertex 4-vertex 3)= ![c,-c/2-h₀*d,-c/2+h₀*d] i := by
  rw [forward_vector]
  fin_cases i <;> simp [nvec,NICertificate.normalValues,dotp] <;> ring

theorem right_dot (c d b : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (rightPoint b-anchor)=
      b*dotp (nvec c d i) (vertex 4-vertex 3) := by
  have he : rightPoint b-anchor=b • (vertex 4-vertex 3) := by
    simp [rightPoint,anchor,AffineMap.lineMap_apply]
  rw [he,dotp_smul_right]

theorem left_dot_projection (c d a : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (leftPoint a-anchor)=
      a*dotp (nvec c d i) (vertex 2-vertex 3) := by
  rw [left_dot,backward_projection]

theorem Pa_dot_zero (a c d : ℝ) :
    dotp (nvec c d 0) (point 0 (-h₀*a)-anchor)=c/2+h₀*d*(1-a) := by
  simp [anchor,vertex_table,nvec,NICertificate.normalValues,dotp]
  ring

theorem Pa_dot_one (a c d : ℝ) :
    dotp (nvec c d 1) (point 0 (-h₀*a)-anchor)=
      c*(1/2-3*a/4)-h₀*d*(1-a/2) := by
  simp [anchor,vertex_table,nvec,NICertificate.normalValues,dotp]
  ring_nf
  rw [ExtremeTriangle.halfRoot_sq]
  ring

theorem window {T : UnitTriangle} {a a3 b : ℝ} (f : Frame T b)
    (ha1 : a<1) (ha3 : a/2<a3) (hb : a<b) (hlight : a3+b<1)
    (hPa : point 0 (-h₀*a)∈T.region) (hleft : leftPoint a3∈T.region) :
    -f.c/2<h₀*f.d ∧ h₀*f.d<f.c/2 := by
  have hp0 := (f.mem _).mp hPa 0
  rw [Pa_dot_zero,f.forward] at hp0
  have hupper := E4T3Scalar.upper_direction f.c_pos ha1 ha3 hlight hp0
  have hp1 := (f.mem _).mp hPa 1
  rw [Pa_dot_one] at hp1
  have hl2 := (f.mem _).mp hleft 2
  rw [left_dot] at hl2
  norm_num at hl2
  have hbudget : f.c*(b+1/2-3*a/4-a3/2)-h₀*f.d*(1-a/2+a3)≤h₀ := by
    have hs := f.sum
    rw [f.forward] at hs
    nlinarith only [hp1,hl2,hs]
  refine ⟨?_,hupper⟩
  by_contra hn
  exact E4T3Scalar.negative_direction_impossible f.c_pos f.unit ha3 hb (le_of_not_gt hn) hbudget

theorem backward_positive_unique {c d : ℝ} (hl : -c/2<h₀*d) (hu : h₀*d<c/2)
    (i : Fin 3) (hi : 0<dotp (nvec c d i) (vertex 2-vertex 3)) : i=1 := by
  rw [backward_projection] at hi
  fin_cases i
  · norm_num at hi
    linarith
  · rfl
  · norm_num at hi
    linarith

theorem forward_positive_unique {c d : ℝ} (hl : -c/2<h₀*d) (hu : h₀*d<c/2)
    (i : Fin 3) (hi : 0<dotp (nvec c d i) (vertex 4-vertex 3)) : i=0 := by
  rw [forward_projection] at hi
  fin_cases i
  · rfl
  · norm_num at hi
    linarith
  · norm_num at hi
    linarith

theorem Frame.forward_active_unique {T : UnitTriangle} {b : ℝ} (f : Frame T b)
    (hb : 0<b) (hl : -f.c/2<h₀*f.d) (hu : h₀*f.d<f.c/2)
    (i : Fin 3) (hactive : dotp (nvec f.c f.d i) (rightPoint b-anchor)=f.margin i) : i=0 := by
  apply forward_positive_unique hl hu i
  rw [right_dot] at hactive
  by_contra hn
  have hp := mul_nonpos_of_nonneg_of_nonpos hb.le (le_of_not_gt hn)
  linarith [f.positive i]

theorem Frame.backward_active_unique {T : UnitTriangle} {a b : ℝ} (f : Frame T b)
    (ha : 0<a) (hl : -f.c/2<h₀*f.d) (hu : h₀*f.d<f.c/2)
    (i : Fin 3) (hactive : dotp (nvec f.c f.d i) (leftPoint a-anchor)=f.margin i) : i=1 := by
  apply backward_positive_unique hl hu i
  rw [left_dot_projection] at hactive
  by_contra hn
  have hp := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
  linarith [f.positive i]

end
end HexagonCover.E4T3Frame

#print axioms HexagonCover.E4T3Frame.actual_frame
#print axioms HexagonCover.E4T3Frame.window
