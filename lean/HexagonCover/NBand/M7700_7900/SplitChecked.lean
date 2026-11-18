import HexagonCover.NBand.M7700_7900.SplitTree.Run0009

namespace HexagonCover.NBand.M7700_7900.SplitChecked
open OwnerTree HexagonCover.NBand.M7700_7900

theorem tree_checked : check (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M7700_7900.SplitTree.Run0009.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M7700_7900.SplitChecked
