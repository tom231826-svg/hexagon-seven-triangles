import HexagonCover.SmallestN.AllFacts
import HexagonCover.SmallestN.DataTree

/-! The complete original smallest N tree, conditional only on its explicit
packet conditions for one actual configuration. Packet necessity is a separate
geometric theorem; no leaf-soundness or unchecked-certificate premise remains. -/
namespace HexagonCover.SmallestN.Root
open Common Semantics

theorem packet_impossible (config : Fin 7 → UnitTriangle)
    (covered : Covers 1 config) (packet : PacketConditions config) : False := by
  exact OwnerTree.check_sound (fun _ => true) Common.allowed Semantics.leafCheck
    (fun _ => True) (Owns config)
    (fun _ _ => True.intro)
    (legal_coverage config covered packet)
    (leafCheck_sound AllFacts.checked config packet.heavyNonIntrusion)
    DataTree.tree Common.mandatory DataTree.tree_checked packet.mandatory

#print axioms packet_impossible
end HexagonCover.SmallestN.Root
