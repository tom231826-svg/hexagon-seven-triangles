import HexagonCover.N7900.Parameters

/-! Guard mutations are checked in Lean. They test necessary rational safety
conditions; they do not claim every altered radius is geometrically invalid. -/
namespace HexagonCover.N7900.ParameterControls
open Parameters NPacketParameters

theorem authoritative_payload : Common.radiusSquared = parameters.radiusSquared := rfl

theorem reversed_band_rejected : check { parameters with lower := 82/100 } = false := by
  decide +kernel

theorem endpoint_zero_rejected : check { parameters with endpoint := 0 } = false := by
  decide +kernel

theorem upper_one_rejected : check { parameters with upper := 1 } = false := by
  decide +kernel

theorem unsafe_central_radius_rejected :
    check { parameters with centralRadius := 1/2 } = false := by decide +kernel

theorem unsafe_heavy_radius_rejected :
    check { parameters with radiusSquared := 1 } = false := by decide +kernel

theorem wrong_radius_binding_rejected :
    decide (Common.radiusSquared = parameters.radiusSquared^2) = false := by decide +kernel

#print axioms unsafe_heavy_radius_rejected
end HexagonCover.N7900.ParameterControls
