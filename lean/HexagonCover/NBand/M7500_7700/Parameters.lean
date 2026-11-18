import HexagonCover.NPacketParameters
import HexagonCover.NBand.M7500_7700.MandatoryGeometry

/-! The exact rational parameters from the frozen M7500_7700 packet. -/
namespace HexagonCover.NBand.M7500_7700.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 3/4
  upper := 77/100
  endpoint := 7707/20000
  lightUpper := ![2959/10000, 3101/10000, 1663/5000, 1867/5000, 7707/20000]
  centralRadius := 1771/20000
  radiusSquared := 27/64

theorem accepted : NPacketParameters.check parameters = true := by decide +kernel

theorem guards : NPacketParameters.Guards parameters :=
  NPacketParameters.guards_of_check accepted

abbrev Band {config : Fin 7 → UnitTriangle} (h : NormalizedHeavy.Normalized config) :=
  NPacketParameters.Band parameters h

theorem left_parameter_eq : (MandatoryGeometry.leftParameter:ℝ) = 1-(parameters.upper:ℝ) := by
  norm_num [MandatoryGeometry.leftParameter, parameters]

theorem right_parameter_eq (i : Fin 6) :
    (MandatoryGeometry.rightParameter i:ℝ) = NPacketParameters.forwardLength parameters i := by
  fin_cases i <;> norm_num [MandatoryGeometry.rightParameter, NPacketParameters.forwardLength, parameters]

theorem central_radius_eq : MandatoryGeometry.centralRadius = parameters.centralRadius := rfl
theorem authoritative_radius_eq : Common.radiusSquared = parameters.radiusSquared := rfl

#print axioms guards
end HexagonCover.NBand.M7500_7700.Parameters
