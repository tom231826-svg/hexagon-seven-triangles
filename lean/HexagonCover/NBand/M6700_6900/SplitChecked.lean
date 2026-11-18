import HexagonCover.NBand.M6700_6900.SplitTree.Run0005

namespace HexagonCover.NBand.M6700_6900.SplitChecked
open OwnerTree HexagonCover.NBand.M6700_6900

theorem tree_checked : check (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M6700_6900.SplitTree.Run0005.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M6700_6900.SplitChecked
