import HexagonCover.NBand.M7500_7700.SplitTree.Run0026

namespace HexagonCover.NBand.M7500_7700.SplitChecked
open OwnerTree HexagonCover.NBand.M7500_7700

theorem tree_checked : check (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M7500_7700.SplitTree.Run0026.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M7500_7700.SplitChecked
