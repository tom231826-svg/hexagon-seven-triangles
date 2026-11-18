import HexagonCover.E4InsidePositive

/-! All actual central orientations in the raw B,T,L chart of the positive
T4 proof. Only cyclic normal relabelling is used. The actual triangle is never
reflected, independently moved, or replaced by a different witness. -/
namespace HexagonCover.E4InsideFrame
noncomputable section
open TriangleFrame SupportGeometry
local notation "h₀" => NICertificate.halfRoot

def raw (c : ℝ) : Fin 3 → Plane :=
  ![point (2*c) (-1/h₀),point (1-c) ((1+3*c)/(2*h₀)),
    point (-(1+c)) ((1-3*c)/(2*h₀))]

theorem exists_downward_normal {c d : ℝ} (hc : 0 ≤ c) (hu : c^2+d^2=1) :
    ∃k:Fin 3,(nvec c d k) 1 ≤ -1/2 := by
  by_cases hd : d ≤ -1/2
  · exact ⟨0,hd⟩
  · have hd0 : -1/2 ≤ d := le_of_lt (lt_of_not_ge hd)
    have hd1 : d ≤ 1 := by nlinarith [sq_nonneg c]
    have hprod := mul_nonneg (sub_nonneg.mpr hd1) (show 0 ≤ d+1/2 by linarith)
    have hh := ExtremeTriangle.halfRoot_pos
    have hs : (h₀*c)^2=3/4*(1-d^2) := by
      rw [mul_pow,ExtremeTriangle.halfRoot_sq]
      nlinarith only [hu]
    refine ⟨2,?_⟩
    norm_num [nvec,NICertificate.normalValues]
    nlinarith [mul_nonneg hh.le hc]

theorem exists_downward_frame (C : UnitTriangle) :
    ∃x y:ℝ,∃offs:Fin 3→ℝ,
      y ≤ -1/2 ∧ x^2+y^2=1 ∧ offs 0+offs 1+offs 2=h₀ ∧
      ∀p:Plane,p∈C.region ↔ ∀i,dotp (nvec x y i) p ≤ offs i := by
  obtain ⟨c,d,offs,hc,hu,hsum,hmem⟩ := exists_normal_frame C
  obtain ⟨k,hk⟩ := exists_downward_normal hc hu
  refine ⟨(nvec c d k) 0,(nvec c d k) 1,fun i=>offs (k+i),hk,?_,?_,?_⟩
  · have hg := nvec_gram hu k k
    simp only [ite_true] at hg
    change (nvec c d k) 0*(nvec c d k) 0+
      (nvec c d k) 1*(nvec c d k) 1=1 at hg
    nlinarith
  · fin_cases k <;> norm_num <;> linarith
  · intro p
    rw [hmem]
    change (∀i,dotp (nvec c d i) p ≤ offs i) ↔ _
    simp_rw [CornerChart.nvec_cyclic]
    constructor
    · intro hp i; exact hp (k+i)
    · intro hp i; simpa using hp (i-k)

theorem raw_scaled {x y : ℝ} (hy : y < 0) (i : Fin 3) :
    (-h₀*y) • raw (-x/(2*h₀*y)) i=nvec x y i := by
  have hh := ne_of_gt ExtremeTriangle.halfRoot_pos
  have hyn := ne_of_lt hy
  fin_cases i <;> ext j <;> fin_cases j
  all_goals simp [raw,nvec,NICertificate.normalValues]
  all_goals field_simp [hh,hyn]
  all_goals ring_nf
  all_goals simp only [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem raw_parameter_bounds {x y : ℝ} (hy : y ≤ -1/2) (hu : x^2+y^2=1) :
    -1 ≤ -x/(2*h₀*y) ∧ -x/(2*h₀*y) ≤ 1 := by
  have hy0 : y < 0 := by linarith
  have hhpos := ExtremeTriangle.halfRoot_pos
  have hden : 2*h₀*y < 0 := mul_neg_of_pos_of_neg (by positivity) hy0
  have hysq : 1/4 ≤ y^2 := by nlinarith [sq_nonneg (y+1/2)]
  have hprod : 0 < -2*h₀*y := by nlinarith only [hden]
  have hsq : (-2*h₀*y)^2=3*y^2 := by rw [mul_pow,mul_pow,ExtremeTriangle.halfRoot_sq]; ring
  have hxlo : 2*h₀*y ≤ x := by nlinarith
  have hxhi : x ≤ -2*h₀*y := by nlinarith
  constructor
  · apply (le_div_iff_of_neg hden).mpr
    linarith
  · apply (div_le_iff_of_neg hden).mpr
    linarith

/-- A geometric construction from actual vertices, with every disk bound
proved against that same actual C. The output c ranges over the full period. -/
theorem exists_raw_frame (C : UnitTriangle) {R : ℝ} (hR : 0 ≤ R)
    (disk : Metric.closedBall (0:Plane) R ⊆ C.region) :
    ∃c F:ℝ,∃offs:Fin 3→ℝ,
      -1 ≤ c ∧ c ≤ 1 ∧ 0 ≤ F ∧ F^2=1+3*c^2 ∧
      offs 0+offs 1+offs 2=F ∧
      (∀i,(R/h₀)*F ≤ offs i) ∧
      ∀p:Plane,p∈C.region ↔ ∀i,dotp (raw c i) p ≤ offs i := by
  obtain ⟨x,y,offs,hy,hu,hsum,hmem⟩ := exists_downward_frame C
  have hy0 : y < 0 := by linarith
  have hyne := ne_of_lt hy0
  have hhpos := ExtremeTriangle.halfRoot_pos
  have hh := ne_of_gt hhpos
  have hs : 0 < -h₀*y := mul_pos_of_neg_of_neg (by linarith) hy0
  have hsne := ne_of_gt hs
  obtain ⟨hc0,hc1⟩ := raw_parameter_bounds hy hu
  refine ⟨-x/(2*h₀*y),-1/y,fun i=>offs i/(-h₀*y),hc0,hc1,
    (div_pos_of_neg_of_neg (by norm_num) hy0).le,?_,?_,?_,?_⟩
  · field_simp [hh,hyne]
    ring_nf
    simp only [ExtremeTriangle.halfRoot_sq]
    nlinarith only [hu]
  · rw [←add_div,←add_div,hsum]
    field_simp [hh,hyne]
  · intro i
    have hp : R • nvec x y i∈C.region := by
      apply disk
      rw [Metric.mem_closedBall,dist_zero_right,norm_smul,
        Real.norm_eq_abs,abs_of_nonneg hR,ExteriorLoss.nvec_norm hu,mul_one]
    have htest := (hmem _).mp hp i
    rw [dotp_smul_right,nvec_gram hu i i] at htest
    simp only [ite_true,mul_one] at htest
    apply (le_div_iff₀ hs).mpr
    have he : (R/h₀)*(-1/y)*(-h₀*y)=R := by field_simp [hh,hyne]
    rw [he]
    exact htest
  · intro p
    rw [hmem]
    constructor
    · intro hp i
      apply (le_div_iff₀ hs).mpr
      have he := congrArg (fun n:Plane=>dotp n p) (raw_scaled (x:=x) hy0 i)
      rw [dotp_smul_left] at he
      nlinarith only [hp i,he]
    · intro hp i
      have hi := (le_div_iff₀ hs).mp (hp i)
      have he := congrArg (fun n:Plane=>dotp n p) (raw_scaled (x:=x) hy0 i)
      rw [dotp_smul_left] at he
      nlinarith only [hi,he]

/-- The actual same-C disk, gap endpoint and adopted positive-T4 contact
cannot coexist. No central orientation hypothesis remains. -/
theorem positive_contact_impossible (C : UnitTriangle) {a v R : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hv : a/2 < v)
    (hR : 0 ≤ R) (hδ : a/4 < R/h₀) (hδ1 : R/h₀ < 1/10)
    (disk : Metric.closedBall (0:Plane) R ⊆ C.region)
    (hP : point (1-a/2) (-h₀*a)∈C.region)
    (hD : E4InsideForced.D∈C.region)
    (hK : point (3*v/2) (-h₀*v)∈C.region) : False := by
  obtain ⟨c,F,offs,hc0,hc1,hF,hFsq,hsum,hdisk,hmem⟩ := exists_raw_frame C hR disk
  have hBP := (hmem _).mp hP 0
  have hTP := (hmem _).mp hP 1
  have hTD := (hmem _).mp hD 1
  have hBK := (hmem _).mp hK 0
  have hh := ne_of_gt ExtremeTriangle.halfRoot_pos
  simp [raw,dotp,E4InsideForced.D] at hBP hTP hTD hBK
  field_simp [hh] at hBP hTP hTD hBK
  exact E4InsidePositive.support_budget_impossible ha ha1 hδ hδ1 hc0 hc1 hv hF hFsq
    hsum (hdisk 0) (hdisk 1) (hdisk 2)
    (by nlinarith only [hBP]) (by nlinarith only [hTP])
    (by nlinarith only [hTD]) (by nlinarith only [hBK])

#print axioms positive_contact_impossible

end
end HexagonCover.E4InsideFrame
