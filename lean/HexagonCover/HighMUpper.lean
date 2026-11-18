import HexagonCover.HighMActual
import HexagonCover.HighMCentralMotion

/-! Actual no-gap high-M exclusion. The same normalized configuration supplies
the heavy support line, both residual points, and the central disk. This is a
geometric branch theorem, not the final covering conjecture assembly. -/
namespace HexagonCover.HighMUpper
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates HighMChart HighMPoints
local notation "h₀" => NICertificate.halfRoot

theorem rho_lt_half {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : CommonReach.rho t < t/2 := by
  have hsq := Real.sq_sqrt (CommonReach.radiusSq_pos t).le
  have hs0 := Real.sqrt_nonneg (CommonReach.radiusSq t)
  have hleft : 0 ≤ 1-t/2 := by linarith
  have hstrict : (1-t/2)^2 < (Real.sqrt (CommonReach.radiusSq t))^2 := by
    rw [hsq]
    dsimp [CommonReach.radiusSq]
    nlinarith only [sq_pos_of_pos ht]
  have hs := (sq_lt_sq₀ hleft hs0).mp hstrict
  unfold CommonReach.rho
  linarith

theorem radius_ratio {M D : ℝ} (hM : h₀ ≤ M) (hM1 : M < 1) (hD : h₀*M < D) :
    0 < CommonReach.rho (1-M) ∧ CommonReach.rho (1-M) ≤ 9*D/100 := by
  have hh : (173:ℝ)/200 < h₀ := by
    nlinarith [ExtremeTriangle.halfRoot_sq,ExtremeTriangle.halfRoot_pos]
  have ht : 0 < 1-M := by linarith
  have ht1 : 1-M < 1 := by linarith
  have hr := rho_lt_half ht ht1
  have hd : 3/4 < D := by
    nlinarith [mul_le_mul_of_nonneg_left hM ExtremeTriangle.halfRoot_pos.le,
      ExtremeTriangle.halfRoot_sq]
  exact ⟨(CentralDisk.rho_bounds ht ht1).1,by linarith⟩

theorem impossible {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (hM : h₀ ≤ M h) : False := by
  have hM1 := (structure_bounds h).2.2.2.2.1
  have hMlow : 4/5 < M h := by
    have hh : (4:ℝ)/5 < h₀ := by nlinarith [ExtremeTriangle.halfRoot_sq,ExtremeTriangle.halfRoot_pos]
    linarith
  obtain ⟨w⟩ := HighMChart.actual_normalized h hMlow
  have hmpos : 0 < M h := by linarith
  have hD : 0 < w.D := lt_trans (mul_pos ExtremeTriangle.halfRoot_pos hmpos) w.lower
  have hr := radius_ratio hM hM1 w.lower
  have hp := HighMActual.same_central h nogaps hM w (k:=HighMScalar.q) (Or.inr rfl)
  have hm := HighMActual.same_central h nogaps hM w (k:=-HighMScalar.q) (Or.inl rfl)
  have hb := HighMCentralMotion.bound (rotateConfig config 6) (n:=inward w.r)
    (D:=w.D) (R:=CommonReach.rho (1-M h)) (q:=21/100)
    w.unit hD hr.1.le (HighMNoGap.same_central_disk h)
    (by simpa only [HighMPoints.residual,HighMPoints.tangent,HighMScalar.q] using hp)
    (by simpa only [HighMPoints.residual,HighMPoints.tangent,HighMScalar.q] using hm)
    (Or.inr ⟨rfl,hr.2⟩)
  have hx := HighMNoGap.depth_disk_strict hM hM1 w.lower
  linarith

#print axioms impossible
end
end HexagonCover.HighMUpper
