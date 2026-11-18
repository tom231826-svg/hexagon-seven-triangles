import HexagonCover.NBand.M7100_7300.SplitTree.Run0018

namespace HexagonCover.NBand.M7100_7300.SplitChecked
open OwnerTree HexagonCover.NBand.M7100_7300

theorem tree_checked : check (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.tree Common.mandatory = true :=
  HexagonCover.NBand.M7100_7300.SplitTree.Run0018.checked0000 Common.mandatory
    (contains_of_mask_inclusion _ _ (by decide +kernel))

#print axioms tree_checked
end HexagonCover.NBand.M7100_7300.SplitChecked
