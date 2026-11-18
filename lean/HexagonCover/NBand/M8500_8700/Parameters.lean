import HexagonCover.NPacketParameters
import HexagonCover.NBand.M8500_8700.MandatoryGeometry

/-! The exact rational parameters from the frozen M8500_8700 packet. -/
namespace HexagonCover.NBand.M8500_8700.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 17/20
  upper := 87/100
  endpoint := 5037/20000
  lightUpper := ![589/2500, 5037/20000, 5037/20000, 5037/20000, 5037/20000]
  centralRadius := 1131/20000
  radiusSquared := 867/1600

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
end HexagonCover.NBand.M8500_8700.Parameters
