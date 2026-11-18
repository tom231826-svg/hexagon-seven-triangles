import HexagonCover.NPacketParameters
import HexagonCover.NBand.M6900_7100.MandatoryGeometry

/-! The exact rational parameters from the frozen M6900_7100 packet. -/
namespace HexagonCover.NBand.M6900_7100.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 69/100
  upper := 71/100
  endpoint := 9137/20000
  lightUpper := ![3237/10000, 829/2500, 861/2500, 1843/5000, 4331/10000]
  centralRadius := 2059/20000
  radiusSquared := 14283/40000

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
end HexagonCover.NBand.M6900_7100.Parameters
