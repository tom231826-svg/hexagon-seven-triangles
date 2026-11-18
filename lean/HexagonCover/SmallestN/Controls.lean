import HexagonCover.SmallestN.DataTree
import HexagonCover.NISubsetData.Batch0000

/-! Mutations of the actual smallest-N interfaces. `OwnerTree.Tree` requires
seven total children and has no unresolved constructor. A placeholder for a
required child is therefore the representable omitted-branch mutation.
Radius identity and geometric rejection are separate assertions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace HexagonCover.SmallestN.Controls

def rootChildren : Fin 7 → DataTree.Tree :=
  ![.leaf 0 (Common.fact 0).pointIds 0, .leaf 1 (Common.fact 1).pointIds 1,
    .leaf 2 (Common.fact 2).pointIds 2, .leaf 3 (Common.fact 3).pointIds 3,
    .leaf 4 (Common.fact 4).pointIds 4, .leaf 5 (Common.fact 5).pointIds 5,
    DataTree.node0001]

theorem original_root : DataTree.tree = .branch 110 rootChildren := rfl

def missingOwner : DataTree.Tree := .branch 110
  (fun i => if i = 0 then .leaf 0 [] 0 else rootChildren i)
def wrongOwner : DataTree.Tree := .branch 110
  (fun i => if i = 0 then .leaf 1 (Common.fact 0).pointIds 0 else rootChildren i)
def wrongQuery : DataTree.Tree := .branch 6 rootChildren

theorem missing_owner_rejected : OwnerTree.check (fun _ => true) Common.allowed
    Semantics.leafCheck missingOwner Common.mandatory = false := by decide +kernel
theorem wrong_owner_leaf_rejected : Semantics.leafCheck 1 (Common.fact 0).pointIds 0 = false := by
  decide +kernel
theorem wrong_owner_tree_rejected : OwnerTree.check (fun _ => true) Common.allowed
    Semantics.leafCheck wrongOwner Common.mandatory = false := by decide +kernel
theorem wrong_path_query_rejected : OwnerTree.check (fun _ => true) Common.allowed
    Semantics.leafCheck wrongQuery Common.mandatory = false := by decide +kernel
theorem omitted_mandatory_rejected : OwnerTree.check (fun _ => true) Common.allowed
    Semantics.leafCheck DataTree.tree OwnerTree.emptyPath = false := by decide +kernel

theorem out_of_range_point_value_unrepresentable : ¬ ∃ p : Fin 170, p.val = 170 := by
  rintro ⟨p, hp⟩
  have := p.isLt
  omega

theorem authoritative_radius_identical :
    NISubsetData.Data0000.c0000_radius = Common.radiusSquared := rfl
theorem squared_again_binding_rejected :
    decide (NISubsetData.Data0000.c0000_radius = Common.radiusSquared ^ 2) = false := by
  decide +kernel

/-- This specific smaller-radius mutation fails the geometric checker too.
This does not assert that every smaller radius must fail for every input. -/
theorem squared_again_geometry_rejected :
    SubsetNI.check NISubsetData.Data0000.c0000_points (Common.radiusSquared ^ 2)
      NISubsetData.Batch0000.c0000_certificate = false := by
  decide +kernel

#print axioms missing_owner_rejected
#print axioms wrong_path_query_rejected
#print axioms squared_again_geometry_rejected
end HexagonCover.SmallestN.Controls
