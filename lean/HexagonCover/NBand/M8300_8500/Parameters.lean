import HexagonCover.NPacketParameters
import HexagonCover.NBand.M8300_8500.MandatoryGeometry

/-! The exact rational parameters from the frozen M8300_8500 packet. -/
namespace HexagonCover.NBand.M8300_8500.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 83/100
  upper := 17/20
  endpoint := 1121/4000
  lightUpper := ![499/2000, 2687/10000, 1121/4000, 1121/4000, 1121/4000]
  centralRadius := 51/800
  radiusSquared := 20667/40000

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
end HexagonCover.NBand.M8300_8500.Parameters
