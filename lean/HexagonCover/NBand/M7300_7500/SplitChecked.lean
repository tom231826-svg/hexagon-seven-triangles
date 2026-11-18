import HexagonCover.NBand.M7300_7500.SplitTree.Run0080

namespace HexagonCover.NBand.M7300_7500.SplitChecked
open OwnerTree HexagonCover.NBand.M7300_7500

theorem tree_checked : check (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M7300_7500.SplitTree.Run0080.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M7300_7500.SplitChecked
