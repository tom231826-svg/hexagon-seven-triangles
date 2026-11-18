import HexagonCover.NPacketParameters
import HexagonCover.NBand.M7700_7900.MandatoryGeometry

/-! The exact rational parameters from the frozen M7700_7900 packet. -/
namespace HexagonCover.NBand.M7700_7900.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 77/100
  upper := 79/100
  endpoint := 1441/4000
  lightUpper := ![1427/5000, 3013/10000, 3261/10000, 1441/4000, 1441/4000]
  centralRadius := 1659/20000
  radiusSquared := 17787/40000

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
end HexagonCover.NBand.M7700_7900.Parameters
