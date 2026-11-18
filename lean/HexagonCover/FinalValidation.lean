import HexagonCover.SemanticFinal
import HexagonCover.FinalNIControls
import HexagonCover.Controls
import HexagonCover.SemanticControls
import HexagonCover.QTreeCheckControls
import HexagonCover.QBoundWitnessControls
import HexagonCover.SmallestN.Controls
import HexagonCover.N7900.ParameterControls
import Lean.Util.CollectAxioms

/-! Final imported-declaration axiom audit, including the explicit original
statement and negative controls. This inspection is not itself a substitute
for the separately recorded clean rebuild and empty-kernel replay. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "HexagonCover." then
      let axioms ← collectAxioms name
      let forbidden := axioms.filter fun ax => !allowed.contains ax
      unless forbidden.isEmpty do
        throwError "Forbidden axiom dependencies for {name}: {forbidden}"
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
  logInfo m!"FINAL_LOCAL_DECLARATIONS {declarations}; THEOREMS {theorems}; ALLOWED_AXIOMS_ONLY"

#check HexagonCover.FinalTheorem.cover_conjecture
#check HexagonCover.SemanticFinal.original_statement_iff
#check HexagonCover.SemanticFinal.explicit_no_seven_rigid_placements
#check HexagonCover.FinalTheorem.size_one_is_covered
#print axioms HexagonCover.FinalTheorem.cover_conjecture
#print axioms HexagonCover.SemanticFinal.no_seven_rigid_placements
#print axioms HexagonCover.FinalNIControls.missing_direction_rejected
#print axioms HexagonCover.FinalNIControls.malformed_extreme_rejected
