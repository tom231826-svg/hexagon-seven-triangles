import HexagonCover.E4InsideDisk

/-! Source-exposed simplification of the negative-T4 central obstruction.
The common P4,D,disk orientation bounds already exclude the whole fixed-x
contact ray v≥3a/4. This is a new exact deduction from the adopted same-C
duties, replacing the source's polar-cone/L0 lower-bound route. It does not
replace the actual T4 contact-forcing and v>5a/6 obligations. -/
namespace HexagonCover.E4InsideMidpoint
noncomputable section
open TriangleFrame
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

theorem midpoint_budget_impossible {a δ c v F B T L : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hδ : a/4 < δ) (hδ1 : δ < 1/10)
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hv : 3*a/4 ≤ v)
    (hF : 0 ≤ F) (hFsq : F^2=1+3*c^2)
    (hsum : B+T+L=F) (hBdisk : δ*F ≤ B) (hLdisk : δ*F ≤ L)
    (hBP : a+(2-a)*c ≤ B) (hTP : 1-a-(1+a)*c ≤ T)
    (hTD : 5/6+c/10 ≤ T) (hBK : v+c ≤ B) : False := by
  by_cases hc : 0 ≤ c
  · exact E4InsidePositive.nonnegative_orientation_impossible ha ha1 hδ hδ1 hc hc1 hF hFsq
      (by linarith) (by linarith)
  · have hk : 0 < -c := by linarith
    have hksq : F^2=1+3*(-c)^2 := by nlinarith only [hFsq]
    by_cases hka : a/2 ≤ -c
    · exact E4InsidePositive.negative_large_impossible ha ha1 hδ hδ1 hka (by linarith) hF hksq
        (by nlinarith only [hTP,hBdisk,hLdisk,hsum])
    · have hkas : -c < a/2 := lt_of_not_ge hka
      obtain ⟨hF1,hFu⟩ := E4InsidePositive.scale_bounds hF hksq
      have hδ0 : 0 < δ := by linarith
      have hδF : a/4 < δ*F := by
        nlinarith [mul_nonneg hδ0.le (sub_nonneg.mpr hF1)]
      have hprod := mul_pos hk (show 0 < a+3*c/2 by linarith)
      nlinarith only [hBK,hTP,hLdisk,hsum,hFu,hδF,hv,hprod]

theorem midpoint_contact_impossible (C : UnitTriangle) {a v R : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hv : 3*a/4 ≤ v)
    (hR : 0 ≤ R) (hδ : a/4 < R/h₀) (hδ1 : R/h₀ < 1/10)
    (disk : Metric.closedBall (0:Plane) R ⊆ C.region)
    (hP : point (1-a/2) (-h₀*a)∈C.region)
    (hD : E4InsideForced.D∈C.region)
    (hK : point (1/2) (-h₀*v)∈C.region) : False := by
  obtain ⟨c,F,offs,hc0,hc1,hF,hFsq,hsum,hdisk,hmem⟩ := E4InsideFrame.exists_raw_frame C hR disk
  have hBP := (hmem _).mp hP 0
  have hTP := (hmem _).mp hP 1
  have hTD := (hmem _).mp hD 1
  have hBK := (hmem _).mp hK 0
  have hh := ne_of_gt ExtremeTriangle.halfRoot_pos
  simp [E4InsideFrame.raw,dotp,E4InsideForced.D] at hBP hTP hTD hBK
  field_simp [hh] at hBP hTP hTD hBK
  exact midpoint_budget_impossible ha ha1 hδ hδ1 hc0 hc1 hv hF hFsq hsum
    (hdisk 0) (hdisk 2)
    (by nlinarith only [hBP]) (by nlinarith only [hTP])
    (by nlinarith only [hTD]) (by nlinarith only [hBK])

theorem actual_midpoint_excluded {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    {v : ℝ} (hv : 3*a h.cover 5/4 ≤ v) :
    point (1/2) (-h₀*v)∉(rotateConfig config 6).region := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  obtain ⟨hR,hδ,hδ1⟩ := E4InsideDisk.radius_bounds ha ha1
  intro hK
  apply midpoint_contact_impossible _ ha ha1 hv hR hδ hδ1
    (E4InsideDisk.actual_disk h) ?_ (E4InsideForced.same_central h sole) hK
  have hp := CentralAxis.source_P_mem h ((sole 4).mpr rfl)
  have he : CentralAxis.P (a h.cover 5)=point (1-a h.cover 5/2) (-h₀*a h.cover 5) := by
    ext i
    fin_cases i <;> simp [CentralAxis.P,ExteriorLoss.lowerEndpoint,
      ExteriorLoss.corner,ExteriorLoss.lowerRay] <;> ring
  rwa [he] at hp

#print axioms actual_midpoint_excluded

end
end HexagonCover.E4InsideMidpoint
