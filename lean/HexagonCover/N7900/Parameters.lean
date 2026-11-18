import HexagonCover.NPacketParameters
import HexagonCover.N7900.MandatoryGeometry

/-! The exact rational parameters from the frozen M7900_8100 packet. -/
namespace HexagonCover.N7900.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 79/100
  upper := 81/100
  endpoint := 6687/20000
  lightUpper := ![1371/5000,583/2000,1591/5000,6687/20000,6687/20000]
  centralRadius := 1539/20000
  radiusSquared := 18723/40000

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
end HexagonCover.N7900.Parameters
