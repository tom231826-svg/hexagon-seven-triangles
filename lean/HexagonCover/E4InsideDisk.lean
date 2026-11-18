import HexagonCover.E4InsideFrame

/-! Actual same-C radius and positive-contact exclusion. The disk is obtained
directly at reach a5/2 from all six actual reach lower bounds, so no monotonicity
or replacement of central configurations is needed. -/
namespace HexagonCover.E4InsideDisk
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

theorem radius_bounds {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    0 ≤ CommonReach.rho (a/2) ∧
      a/4 < CommonReach.rho (a/2)/h₀ ∧ CommonReach.rho (a/2)/h₀ < 1/10 := by
  have ht : 0 < a/2 := by linarith
  have ht1 : a/2 < 1 := by linarith
  have hR := CentralDisk.rho_bounds ht ht1
  have hsafe := IntruderReach.rho_gt_safe_radius ht ht1
  have hpos := ExtremeTriangle.halfRoot_pos
  have hsq := ExtremeTriangle.halfRoot_sq
  have hhlo : 4/5 < h₀ := by nlinarith
  have hhhi : h₀ < 7/8 := by nlinarith
  have hroot := Real.sq_sqrt (CommonReach.radiusSq_pos (a/2)).le
  have hroot0 := Real.sqrt_nonneg (CommonReach.radiusSq (a/2))
  have hRlt : CommonReach.rho (a/2) < a/2 := by
    unfold CommonReach.rho CommonReach.radiusSq
    dsimp only [CommonReach.radiusSq] at hroot hroot0
    nlinarith
  refine ⟨hR.1.le,?_,?_⟩
  · apply (lt_div_iff₀ hpos).mpr
    have hp := mul_pos ha (show 0 < 1-4*a by linarith)
    have hq := mul_pos ha (show 0 < 7/8-h₀ by linarith)
    nlinarith only [hsafe,hp,hq]
  · apply (div_lt_iff₀ hpos).mpr
    linarith

theorem actual_disk {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    Metric.closedBall (0:Plane) (CommonReach.rho (a h.cover 5/2)) ⊆
      (rotateConfig config 6).region := by
  have ha := (leftReach h.cover 5).positive
  have ha1 := (leftReach h.cover 5).lt_one
  change 0 < a h.cover 5 at ha
  change a h.cover 5 < 1 at ha1
  have hs := GapChains.heavy_short h
  have hl := (structure_bounds h).1
  apply SourceCoordinates.central_disk
  apply CentralDisk.actual_central_disk_of_reach_lower h.cover (by linarith) (by linarith)
  intro i
  exact le_trans (by linarith : a h.cover 5/2 ≤ 1-M h) (hl i)

/-- The same actual C excludes every adopted contact point with v>a5/2.
The remaining positive-T4 task is to derive such a contact from the actual
finite T4 side and to force that contact into this same C. -/
theorem actual_contact_excluded {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    {v : ℝ} (hv : a h.cover 5/2 < v) :
    point (3*v/2) (-h₀*v)∉(rotateConfig config 6).region := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  obtain ⟨hR,hδ,hδ1⟩ := radius_bounds ha ha1
  intro hK
  apply E4InsideFrame.positive_contact_impossible _ ha ha1 hv hR hδ hδ1
    (actual_disk h) ?_ (E4InsideForced.same_central h sole) hK
  have hp := CentralAxis.source_P_mem h ((sole 4).mpr rfl)
  have he : CentralAxis.P (a h.cover 5)=point (1-a h.cover 5/2) (-h₀*a h.cover 5) := by
    ext i
    fin_cases i <;> simp [CentralAxis.P,ExteriorLoss.lowerEndpoint,
      ExteriorLoss.corner,ExteriorLoss.lowerRay] <;> ring
  rwa [he] at hp

#print axioms actual_contact_excluded

end
end HexagonCover.E4InsideDisk
