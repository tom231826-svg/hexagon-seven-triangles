import HexagonCover.QTreeCheck

set_option maxRecDepth 100000

namespace HexagonCover.QTreeCheckControls
open DistanceLeaf DistanceData QCertificate QTreeCheck

/-- The actual Q25 fact 0 and its existing exact diameter witness. -/
def row : Row .q25 := ⟨0, false, 0, [⟨0, by decide⟩]⟩

theorem row_checked : Checked row := by
  apply Checked.diameter (0, 1)
  exact q25Fact0_witness_check

def lookup (token : Nat) : Option (Row .q25) :=
  if token = 0 then some row else none

theorem original : leafCheck lookup 0 [253, 0] 0 = true := by decide +kernel

theorem wrong_owner : leafCheck lookup 1 [253, 0] 0 = false := by decide +kernel

theorem wrong_flag : leafCheck lookup 0 [253, 0] (2 ^ 40) = false := by decide +kernel

theorem wrong_point : leafCheck lookup 0 [253, 1] 0 = false := by decide +kernel

theorem missing_anchor : leafCheck lookup 0 [0] 0 = false := by decide +kernel

end HexagonCover.QTreeCheckControls
