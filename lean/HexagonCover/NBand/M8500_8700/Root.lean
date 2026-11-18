import HexagonCover.NBand.M8500_8700.AllFacts
import HexagonCover.NBand.M8500_8700.SplitChecked

/-! The complete original M8500_8700 N tree, conditional only on its explicit
packet conditions for one actual configuration. Packet necessity is a separate
geometric theorem; no leaf-soundness or unchecked-certificate premise remains. -/
namespace HexagonCover.NBand.M8500_8700.Root
open Common Semantics

theorem packet_impossible (config : Fin 7 → UnitTriangle)
    (covered : Covers 1 config) (packet : PacketConditions config) : False := by
  exact OwnerTree.check_sound (fun _ => true) Common.allowed Semantics.leafCheck
    (fun _ => True) (Owns config)
    (fun _ _ => True.intro)
    (legal_coverage config covered packet)
    (leafCheck_sound AllFacts.checked config packet.heavyNonIntrusion)
    SplitData.tree Common.mandatory SplitChecked.tree_checked packet.mandatory

#print axioms packet_impossible
end HexagonCover.NBand.M8500_8700.Root
