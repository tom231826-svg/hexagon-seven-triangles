import HexagonCover.N7900.SplitAlignedTree.Run0029

namespace HexagonCover.N7900.SplitAlignedChecked
open OwnerTree HexagonCover.N7900

theorem tree_checked : check (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck HexagonCover.N7900.SplitData.tree Common.mandatory = true :=
  HexagonCover.N7900.SplitAlignedTree.Run0029.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.N7900.SplitAlignedChecked
