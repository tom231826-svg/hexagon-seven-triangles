import HexagonCover.NBand.M6667_6700.SplitTree.Run0053

namespace HexagonCover.NBand.M6667_6700.SplitChecked
open OwnerTree HexagonCover.NBand.M6667_6700

theorem tree_checked : check (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M6667_6700.SplitTree.Run0053.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M6667_6700.SplitChecked
