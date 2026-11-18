import HexagonCover.NPacketParameters
import HexagonCover.NBand.M6700_6900.MandatoryGeometry

/-! The exact rational parameters from the frozen M6700_6900 packet. -/
namespace HexagonCover.NBand.M6700_6900.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 67/100
  upper := 69/100
  endpoint := 9589/20000
  lightUpper := ![83/250, 3373/10000, 3459/10000, 29/80, 4083/10000]
  centralRadius := 2139/20000
  radiusSquared := 13467/40000

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
end HexagonCover.NBand.M6700_6900.Parameters
