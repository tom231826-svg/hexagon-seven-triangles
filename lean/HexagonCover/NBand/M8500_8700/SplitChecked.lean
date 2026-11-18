import HexagonCover.NBand.M8500_8700.SplitTree.Run0099

namespace HexagonCover.NBand.M8500_8700.SplitChecked
open OwnerTree HexagonCover.NBand.M8500_8700

theorem tree_checked : check (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M8500_8700.SplitTree.Run0099.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M8500_8700.SplitChecked
