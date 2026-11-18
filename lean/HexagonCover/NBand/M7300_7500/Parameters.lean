import HexagonCover.NPacketParameters
import HexagonCover.NBand.M7300_7500.MandatoryGeometry

/-! The exact rational parameters from the frozen M7300_7500 packet. -/
namespace HexagonCover.NBand.M7300_7500.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 73/100
  upper := 3/4
  endpoint := 8197/20000
  lightUpper := ![3057/10000, 3181/10000, 3377/10000, 3739/10000, 8197/20000]
  centralRadius := 3/32
  radiusSquared := 15987/40000

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
end HexagonCover.NBand.M7300_7500.Parameters
