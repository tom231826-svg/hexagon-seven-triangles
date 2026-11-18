import HexagonCover.NPacketParameters
import HexagonCover.NBand.M6667_6700.MandatoryGeometry

/-! The exact rational parameters from the frozen M6667_6700 packet. -/
namespace HexagonCover.NBand.M6667_6700.Parameters

def parameters : NPacketParameters.Parameters where
  lower := 2/3
  upper := 67/100
  endpoint := 2899/6000
  lightUpper := ![1667/5000, 1671/5000, 839/2500, 3383/10000, 433/1250]
  centralRadius := 2211/20000
  radiusSquared := 1/3

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
end HexagonCover.NBand.M6667_6700.Parameters
