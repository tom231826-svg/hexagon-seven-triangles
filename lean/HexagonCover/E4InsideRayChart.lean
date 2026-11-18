import HexagonCover.E4InsideSourceActive

/-! Generic clockwise-120-degree two-ray chart derived from one actual
backward-active side. No direction interval or uniqueness is assumed. T1,
T2 and T4 use this same chart in their own actual source-coordinate poses. -/
namespace HexagonCover.E4InsideRayChart
noncomputable section
open TriangleFrame SupportGeometry
open HexagonCover.Configuration SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def rows (r L K : ℝ) : Fin 3→ℝ :=
  ![L-(1+r)*K,-(1+r)*L+r*K,r*L+K]

structure Chart (T : UnitTriangle) (U p q : Plane) (s : ℝ) where
  r : ℝ
  d : ℝ
  e : ℝ
  D : ℝ
  first_pos : 0 < s
  d_pos : 0 < d
  e_pos : 0 < e
  D_pos : 0 < D
  D_sq : D^2=1+r+r^2
  margin_sum : s+d+e=D
  character : ∀L K,U+L • p+K • q∈T.region ↔ ∀i,rows r L K i ≤ ![s,d,e] i
  strict_tests : ∀L K,U+L • p+K • q∈interior T.region →
    ∀i,rows r L K i < ![s,d,e] i

theorem interior_support_strict (T : UnitTriangle) {c d : ℝ} {offs : Fin 3→ℝ}
    (hu : c^2+d^2=1)
    (hmem : ∀p:Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i)
    {p : Plane} (hp : p∈interior T.region) (i : Fin 3) : dotp (nvec c d i) p < offs i := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hm := E4InsideActive.anchor_margin_pos T hε hball hu hmem i
  linarith

theorem projection_left (c d u v : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (point u v)=
      ![dotp (nvec c d 0) (point u v),dotp (nvec c d 0) (nvec u v 2),
        -dotp (nvec c d 0) (point u v)-dotp (nvec c d 0) (nvec u v 2)] i := by
  fin_cases i <;> simp [dotp,nvec,NICertificate.normalValues] <;> ring

theorem projection_right (c d u v : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (nvec u v 2)=
      ![dotp (nvec c d 0) (nvec u v 2),
        -dotp (nvec c d 0) (point u v)-dotp (nvec c d 0) (nvec u v 2),
        dotp (nvec c d 0) (point u v)] i := by
  fin_cases i <;> simp [dotp,nvec,NICertificate.normalValues]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem projection_quadratic {c d u v : ℝ} (hn : c^2+d^2=1) (hp : u^2+v^2=1) :
    (dotp (nvec c d 0) (point u v))^2+
      dotp (nvec c d 0) (point u v)*dotp (nvec c d 0) (nvec u v 2)+
      (dotp (nvec c d 0) (nvec u v 2))^2=h₀^2 := by
  have he : (dotp (nvec c d 0) (point u v))^2+
      dotp (nvec c d 0) (point u v)*dotp (nvec c d 0) (nvec u v 2)+
      (dotp (nvec c d 0) (nvec u v 2))^2=
      (3/4:ℝ)*(c^2+d^2)*(u^2+v^2) := by
    simp [dotp,nvec,NICertificate.normalValues]
    ring_nf
    simp only [ExtremeTriangle.halfRoot_sq]
    ring
  rw [he,hn,hp,ExtremeTriangle.halfRoot_sq]
  ring

theorem of_active (T : UnitTriangle) (U : Plane) {s c d u v ε : ℝ}
    {offs : Fin 3→ℝ} (hn : c^2+d^2=1) (hp : u^2+v^2=1)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (hmem : ∀z:Plane,z∈T.region ↔ ∀i,dotp (nvec c d i) z ≤ offs i)
    (hε : 0 < ε) (hball : Metric.ball U ε ⊆ T.region)
    (hx : 0 < dotp (nvec c d 0) (point u v))
    (hactive : dotp (nvec c d 0) (U+s • point u v)=offs 0) :
    Nonempty (Chart T U (point u v) (nvec u v 2) s) := by
  let x : ℝ := dotp (nvec c d 0) (point u v)
  let y : ℝ := dotp (nvec c d 0) (nvec u v 2)
  let r : ℝ := -1-y/x
  let m : Fin 3→ℝ := fun i=>(offs i-dotp (nvec c d i) U)/x
  have hx0 : 0 < x := hx
  have hxne : x≠0 := ne_of_gt hx0
  have hmpos (i:Fin 3) : 0 < m i :=
    div_pos (E4InsideActive.anchor_margin_pos T hε hball hn hmem i) hx0
  have hm0 : m 0=s := by
    apply (div_eq_iff hxne).mpr
    rw [dotp_add_right,dotp_smul_right] at hactive
    change dotp (nvec c d 0) U+s*x=offs 0 at hactive
    linarith
  have hmvec : m=![s,m 1,m 2] := by
    funext i
    fin_cases i
    · exact hm0
    · rfl
    · rfl
  have hDpos : 0 < h₀/x := div_pos ExtremeTriangle.halfRoot_pos hx0
  have hDsq : (h₀/x)^2=1+r+r^2 := by
    have hq := projection_quadratic hn hp
    change x^2+x*y+y^2=h₀^2 at hq
    dsimp only [r]
    field_simp [hxne]
    nlinarith only [hq]
  have hmsum : s+m 1+m 2=h₀/x := by
    have hdot := dot_nvec_sum c d U
    rw [Fin.sum_univ_three] at hdot
    rw [←hm0]
    dsimp only [m]
    rw [←add_div,←add_div]
    congr 1
    linarith
  have hrow (L K:ℝ) (i:Fin 3) :
      dotp (nvec c d i) (L • point u v+K • nvec u v 2)=x*rows r L K i := by
    rw [dotp_add_right,dotp_smul_right,dotp_smul_right]
    have he := congrArg₂ (fun l rr : ℝ=>L*l+K*rr)
      (projection_left c d u v i) (projection_right c d u v i)
    change L*dotp (nvec c d i) (point u v)+K*dotp (nvec c d i) (nvec u v 2)=
      L*(![x,y,-x-y] i)+K*(![y,-x-y,x] i) at he
    rw [he]
    fin_cases i <;> simp [rows,r]
    all_goals field_simp [hxne] <;> ring
  have hpoint (L K:ℝ) (i:Fin 3) :
      dotp (nvec c d i) (U+L • point u v+K • nvec u v 2)=
        dotp (nvec c d i) U+x*rows r L K i := by
    rw [add_assoc,dotp_add_right,hrow]
  refine ⟨⟨r,m 1,m 2,h₀/x,by simpa only [hm0] using hmpos 0,
    hmpos 1,hmpos 2,hDpos,hDsq,hmsum,?_,?_⟩⟩
  · intro L K
    rw [hmem,←hmvec]
    constructor
    · intro hz i
      apply (le_div_iff₀ hx0).mpr
      have hi := hz i
      rw [hpoint] at hi
      nlinarith only [hi]
    · intro hz i
      have hi := (le_div_iff₀ hx0).mp (hz i)
      rw [hpoint]
      nlinarith only [hi]
  · intro L K hz i
    rw [←hmvec]
    apply (lt_div_iff₀ hx0).mpr
    have hi := interior_support_strict T hn hmem hz i
    rw [hpoint] at hi
    nlinarith only [hi]

/-- The true finite forward exit activates at least one of the three raw
rows; ties are retained as a disjunction, with no sign or tilt restriction. -/
theorem Chart.forward_exit_active {T : UnitTriangle} {U p q : Plane} {s b : ℝ}
    (ch : Chart T U p q s) (hb : 0 < b) (hb1 : b < 1)
    (hmax : ∀t∈Set.Icc (0:ℝ) 1,U+t • q∈T.region ↔ t ≤ b) :
    -(1+ch.r)*b=s ∨ ch.r*b=ch.d ∨ b=ch.e := by
  have hpoint : U+(0:ℝ) • p+b • q∈T.region := by simpa using (hmax b ⟨hb.le,hb1.le⟩).mpr le_rfl
  have htests := (ch.character 0 b).mp hpoint
  by_contra hn
  push Not at hn
  have hstrict : ∀i,rows ch.r 0 b i < ![s,ch.d,ch.e] i := by
    intro i
    have hi := htests i
    fin_cases i
    · simp [rows] at hi ⊢
      exact lt_of_le_of_ne hi (by simpa only [neg_mul] using hn.1)
    · simp [rows] at hi ⊢
      exact lt_of_le_of_ne hi hn.2.1
    · simp [rows] at hi ⊢
      exact lt_of_le_of_ne hi hn.2.2
  let V : Set ℝ := {t | ∀i,rows ch.r 0 t i < ![s,ch.d,ch.e] i}
  have hopen : IsOpen V := by
    have he : V=⋂i:Fin 3,{t:ℝ | rows ch.r 0 t i < ![s,ch.d,ch.e] i} := by ext t; simp [V]
    rw [he]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt
    · fin_cases i <;> simp [rows] <;> fun_prop
    · fun_prop
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen b hstrict
  let w : ℝ := min (ε/2) ((1-b)/2)
  have hw : 0 < w := lt_min (by linarith) (by linarith)
  have hwε : w < ε := (min_le_left _ _).trans_lt (by linarith)
  have hwb : b+w ≤ 1 := by
    have hm := min_le_right (ε/2) ((1-b)/2)
    change w ≤ (1-b)/2 at hm
    linarith
  have hv : b+w∈V := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos hw]
    exact hwε
  have hm : U+(b+w) • q∈T.region := by
    have hh := (ch.character 0 (b+w)).mpr (fun i=>(hv i).le)
    simpa using hh
  have hh := (hmax (b+w) ⟨by linarith,hwb⟩).mp hm
  linarith

#print axioms of_active
#print axioms Chart.forward_exit_active

end
end HexagonCover.E4InsideRayChart
