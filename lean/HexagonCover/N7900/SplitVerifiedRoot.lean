import HexagonCover.N7900.AllFactsChecked
import HexagonCover.N7900.SplitAlignedChecked

/-! The complete original M7900_8100 N tree, conditional only on its explicit
packet conditions for one actual configuration. Packet necessity is a separate
geometric theorem; no leaf-soundness or unchecked-certificate premise remains. -/
namespace HexagonCover.N7900.SplitVerifiedRoot
open Common Semantics

theorem packet_impossible (config : Fin 7 → UnitTriangle)
    (covered : Covers 1 config) (packet : PacketConditions config) : False := by
  exact OwnerTree.check_sound (fun _ => true) Common.allowed Semantics.leafCheck
    (fun _ => True) (Owns config)
    (fun _ _ => True.intro)
    (legal_coverage config covered packet)
    (leafCheck_sound AllFactsChecked.checked config packet.heavyNonIntrusion)
    SplitData.tree Common.mandatory SplitAlignedChecked.tree_checked packet.mandatory

#print axioms packet_impossible
end HexagonCover.N7900.SplitVerifiedRoot
