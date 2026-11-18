import HexagonCover.NBand.M8300_8500.SplitTree.Run0108

namespace HexagonCover.NBand.M8300_8500.SplitChecked
open OwnerTree HexagonCover.NBand.M8300_8500

theorem tree_checked : check (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M8300_8500.SplitTree.Run0108.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M8300_8500.SplitChecked
