import HexagonCover.ExteriorLoss

/-! Weak finite-event bounds with an equality obstruction at a strict origin.
Unlike a strict enclosure certificate, this preserves genuine unit equality
packets and excludes them only when the same actual triangle contains a
positive origin ball. Existing strict event consumers remain unchanged. -/
namespace HexagonCover.SupportGeometryWeak
noncomputable section
open SupportGeometry TriangleFrame
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def WeakEventBound (points : ι → Plane) (bound : ℝ) : Prop :=
  ∀j k,points j≠points k → ∀i:Fin 3,∀negative:Bool,
    bound*‖points k-points j‖ ≤
      total points ((eventBase (points j) (points k) i negative) 0)
        ((eventBase (points j) (points k) i negative) 1)

/-- Equality at an event forces a support line through the origin. -/
def OriginCertificate (points : ι → Plane) (bound : ℝ) : Prop :=
  ∀j k,points j≠points k → ∀i:Fin 3,∀negative:Bool,
    let raw := eventBase (points j) (points k) i negative
    bound*‖points k-points j‖ ≤ total points (raw 0) (raw 1) ∧
      (total points (raw 0) (raw 1) ≤ bound*‖points k-points j‖ →
        ∃l:Fin 3,support points (raw 0) (raw 1) l=0)

/-- Any selected support branch is a valid lower bound; if equality is possible,
a selected origin gives the required zero support. Selection itself is untrusted. -/
theorem rigidity_of_branch (points : ι → Plane) (f : Fin 3 → ι) (c d bound : ℝ)
    (hlower : bound ≤ branch points f c d)
    (hcase : bound < branch points f c d ∨ ∃i,points (f i)=0) :
    bound ≤ total points c d ∧ (total points c d ≤ bound → ∃i,support points c d i=0) := by
  have hle := branch_le_total points f c d
  refine ⟨hlower.trans hle,?_⟩
  intro hupper
  rcases hcase with hstrict | ⟨i,hi⟩
  · exact (not_lt_of_ge hupper (hstrict.trans_le hle)).elim
  · have he : branch points f c d=total points c d := le_antisymm hle (hupper.trans hlower)
    have hactive := active_component points f c d he i
    rw [hi] at hactive
    refine ⟨i,?_⟩
    simpa [dotp] using hactive.symm

theorem bound_of_events (points : ι → Plane) {a b : ι}
    (hab : points a≠points b) {bound : ℝ} (hevents : WeakEventBound points bound) :
    ∀θ:ℝ,bound ≤ total points (Real.cos θ) (Real.sin θ) := by
  obtain ⟨φ,i,j,k,hjk,hj,hk,hmin⟩ := minimum_at_support_pair_of_distinct points hab
  obtain ⟨negative,hscale⟩ := total_event_scale points (Real.cos_sq_add_sin_sq φ) hjk i
    (hj.trans hk.symm)
  have hb := hevents j k hjk i negative
  rw [hscale] at hb
  have hr : 0 < ‖points k-points j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hjk.symm)
  have hφ : bound ≤ total points (Real.cos φ) (Real.sin φ) := by
    apply (mul_le_mul_iff_of_pos_left hr).mp
    simpa only [mul_comm bound ‖points k-points j‖] using hb
  exact fun θ => hφ.trans (hmin θ)

theorem semicircle_angle {c d : ℝ} (hu : c^2+d^2=1) (hc : 0 ≤ c) :
    ∃θ:ℝ,Real.cos θ=c ∧ Real.sin θ=d := by
  have hd0 : -1 ≤ d := by nlinarith [sq_nonneg c]
  have hd1 : d ≤ 1 := by nlinarith [sq_nonneg c]
  have hs := Real.sin_arcsin hd0 hd1
  refine ⟨Real.arcsin d,?_,hs⟩
  have hunit := Real.cos_sq_add_sin_sq (Real.arcsin d)
  rw [hs] at hunit
  nlinarith [Real.cos_arcsin_nonneg d]

/-- A prescribed minimizing angle, not merely some minimizer, has a tied pair. -/
theorem support_pair_at_minimum (points : ι → Plane) (hinj : Function.Injective points)
    {a b : ι} (hab : a≠b) (θ : ℝ)
    (hmin : ∀φ:ℝ,total points (Real.cos θ) (Real.sin θ) ≤
      total points (Real.cos φ) (Real.sin φ)) :
    ∃i:Fin 3,∃j k:ι,points j≠points k ∧
      dotp (nvec (Real.cos θ) (Real.sin θ) i) (points j)=
        support points (Real.cos θ) (Real.sin θ) i ∧
      dotp (nvec (Real.cos θ) (Real.sin θ) i) (points k)=
        support points (Real.cos θ) (Real.sin θ) i := by
  have hpos : 0 < SupportEvents.envelope
      (fun f:Fin 3→ι => SupportEvents.trigLinear (branchA points f) (branchB points f)) θ := by
    rw [envelope_eq_total]
    exact total_pos points (Real.cos_sq_add_sin_sq θ) (hinj.ne hab)
  have hlocal : IsLocalMin (SupportEvents.envelope
      (fun f:Fin 3→ι => SupportEvents.trigLinear (branchA points f) (branchB points f))) θ := by
    apply Filter.Eventually.of_forall
    intro φ
    simpa only [envelope_eq_total] using hmin φ
  obtain ⟨f,g,hfg,hf,hg⟩ := SupportEvents.trig_envelope_min_has_tie
    (branchA points) (branchB points) θ hlocal hpos
  have hfa : branch points f (Real.cos θ) (Real.sin θ)=total points (Real.cos θ) (Real.sin θ) := by
    simpa only [trig_branch,envelope_eq_total] using hf
  have hga : branch points g (Real.cos θ) (Real.sin θ)=total points (Real.cos θ) (Real.sin θ) := by
    simpa only [trig_branch,envelope_eq_total] using hg
  have hd : ∃i,f i≠g i := by
    by_contra hn
    push Not at hn
    exact hfg (funext hn)
  obtain ⟨i,hi⟩ := hd
  exact ⟨i,f i,g i,hinj.ne hi,active_component points f _ _ hfa i,
    active_component points g _ _ hga i⟩

theorem frame_offset_pos (T : UnitTriangle) {c d r : ℝ} {offs : Fin 3 → ℝ}
    (hu : c^2+d^2=1) (hr : 0 < r) (hball : Metric.ball (0:Plane) r ⊆ T.region)
    (hmem : ∀p:Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i) (i : Fin 3) :
    0 < offs i := by
  let p : Plane := (r/2) • nvec c d i
  have ht : 0 < r/2 := by linarith
  have hn : ‖p‖=r/2 := by
    simp only [p,norm_smul,Real.norm_eq_abs,abs_of_pos ht,ExteriorLoss.nvec_norm hu,mul_one]
  have hp : p∈T.region := by
    apply hball
    rw [Metric.mem_ball,dist_zero_right,hn]
    linarith
  have hh := (hmem p).mp hp i
  have he : dotp (nvec c d i) p=r/2 := by
    rw [dotp_smul_right,nvec_gram hu i i]
    simp
  rw [he] at hh
  exact ht.trans_le hh

/-- Weak packet size plus exact event equality obstruction excludes a unit
triangle only with its actual strict origin ball. -/
theorem cannot_contain_with_origin_ball (points : ι → Plane)
    (hinj : Function.Injective points) {a b : ι} (hab : a≠b)
    (events : OriginCertificate points NICertificate.halfRoot)
    (T : UnitTriangle) {r : ℝ} (hr : 0 < r) (hball : Metric.ball (0:Plane) r ⊆ T.region)
    (hcontained : ∀j,points j∈T.region) : False := by
  obtain ⟨c,d,offs,hc,hu,hsum,hmem⟩ := TriangleFrame.exists_normal_frame T
  have hmem' : ∀p:Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i := hmem
  have hs (i : Fin 3) : support points c d i ≤ offs i := by
    apply Finset.sup'_le
    intro j _
    exact (hmem' (points j)).mp (hcontained j) i
  have hupper : total points c d ≤ NICertificate.halfRoot := by
    simp only [total,Fin.sum_univ_three]
    linarith [hs 0,hs 1,hs 2]
  have hweak : WeakEventBound points NICertificate.halfRoot :=
    fun j k hjk i neg => (events j k hjk i neg).1
  have hb := bound_of_events points (hinj.ne hab) hweak
  obtain ⟨θ,hcos,hsin⟩ := semicircle_angle hu hc
  have htotal : total points c d=NICertificate.halfRoot := by
    have hl := hb θ
    rw [hcos,hsin] at hl
    exact le_antisymm hupper hl
  have hmin : ∀φ:ℝ,total points (Real.cos θ) (Real.sin θ) ≤
      total points (Real.cos φ) (Real.sin φ) := by
    intro φ
    rw [hcos,hsin,htotal]
    exact hb φ
  obtain ⟨i,j,k,hjk,hj,hk⟩ := support_pair_at_minimum points hinj hab θ hmin
  rw [hcos,hsin] at hj hk
  obtain ⟨neg,he⟩ := normalized_event hu hjk i (hj.trans hk.symm)
  have hrnorm : 0 < ‖points k-points j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hjk.symm)
  have hscaled := congrArg (fun n:Plane => ‖points k-points j‖ • n) he
  have hraw : eventBase (points j) (points k) i neg=‖points k-points j‖ • point c d := by
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hrnorm),one_smul] using hscaled.symm
  have hcert := events j k hjk i neg
  obtain ⟨l,hzero⟩ := hcert.2 (by
    dsimp
    rw [hraw]
    simp only [PiLp.smul_apply,smul_eq_mul,point_coord_zero,point_coord_one]
    rw [total_smul points hrnorm.le,htotal]
    exact le_of_eq (mul_comm _ _))
  rw [hraw] at hzero
  simp only [PiLp.smul_apply,smul_eq_mul,point_coord_zero,point_coord_one] at hzero
  rw [support_smul points hrnorm.le] at hzero
  have hz : support points c d l=0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hrnorm)
  have hssum : ∑i:Fin 3,support points c d i=NICertificate.halfRoot := htotal
  have hosum : ∑i:Fin 3,offs i=NICertificate.halfRoot := by
    simpa only [Fin.sum_univ_three] using hsum
  have hdiffsum : ∑i:Fin 3,(offs i-support points c d i)=0 := by
    rw [Finset.sum_sub_distrib,hosum,hssum,sub_self]
  have hdiff := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (i:Fin 3) _ => sub_nonneg.mpr (hs i))).mp hdiffsum l (Finset.mem_univ l)
  have hpos := frame_offset_pos T hu hr hball hmem' l
  rw [hz] at hdiff
  linarith

end
end HexagonCover.SupportGeometryWeak
