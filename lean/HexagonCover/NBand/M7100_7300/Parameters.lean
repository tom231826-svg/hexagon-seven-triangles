import HexagonCover.NPacketParameters
import HexagonCover.NBand.M7100_7300.MandatoryGeometry

/-! The exact rational parameters from the frozen M7100_7300 packet. -/
namespace HexagonCover.NBand.M7100_7300.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 71/100
  upper := 73/100
  endpoint := 8673/20000
  lightUpper := ![63/200, 813/2500, 3417/10000, 3723/10000, 8673/20000]
  centralRadius := 1971/20000
  radiusSquared := 15123/40000

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
end HexagonCover.NBand.M7100_7300.Parameters
