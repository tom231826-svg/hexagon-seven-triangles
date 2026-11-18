import HexagonCover.NBand.M8300_8500.Common
import HexagonCover.HexDomain

/-! The same-configuration semantics for the raw M8300_8500 packet.
The N anchor convention is rotated by +60 degrees relative to the Q convention;
this module makes no identification between those conventions. -/
namespace HexagonCover.NBand.M8300_8500.Semantics
open DistanceLeaf Common

def Owns (config : Fin 7 → UnitTriangle) (owner : Fin 7) (p : Fin 177) : Prop :=
  toPlane (Common.point p) ∈ (config owner).region

def NonIntrusion (T : UnitTriangle) : Prop :=
  ∀ z ∈ T.region, (radiusSquared : ℝ) ≤ ‖z‖ ^ 2

/-- Only the original role 5 carries the packet's nonintrusion condition. -/
structure CheckedFact (i : Fin 1786) : Prop where
  excluded : ∀ T : UnitTriangle,
    (∀ p ∈ obligations i, toPlane p ∈ T.region) →
    ((fact i).role = 5 → NonIntrusion T) → False

def leafCheck (owner : Fin 7) (ids : List (Fin 177)) (i : Fin 1786) : Bool :=
  decide (owner = (fact i).role ∧ ids = (fact i).pointIds)

theorem leafCheck_sound (proofs : ∀ i, CheckedFact i)
    (config : Fin 7 → UnitTriangle) (hNI : NonIntrusion (config 5))
    (owner : Fin 7) (ids : List (Fin 177)) (i : Fin 1786)
    (accepted : leafCheck owner ids i = true)
    (contained : ∀ p ∈ ids, Owns config owner p) : False := by
  obtain ⟨howner, hids⟩ := of_decide_eq_true accepted
  apply (proofs i).excluded (config owner)
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact contained j (by simpa only [hids] using hj)
  · intro hrole
    simpa only [howner, hrole] using hNI

theorem all_points_checked : ∀ i : Fin 177, HexDomain.check (Common.point i) = true := by
  decide +kernel

theorem all_points_in_hexagon (i : Fin 177) : toPlane (Common.point i) ∈ Hexagon 1 :=
  HexDomain.check_sound _ (all_points_checked i)

/-- Exact packet assumptions on a single actual configuration. Outer-only
coverage is requested precisely at IDs where the original allowed-role table
excludes role 6. Overlap and multiple possible owners remain permitted. -/
structure PacketConditions (config : Fin 7 → UnitTriangle) : Prop where
  mandatory : OwnerTree.Satisfies (Owns config) Common.mandatory
  outerCoverage : ∀ p : Fin 177, Common.allowed p 6 = false →
    ∃ owner : Fin 7, owner.val < 6 ∧ Owns config owner p
  heavyNonIntrusion : NonIntrusion (config 5)

theorem legal_coverage (config : Fin 7 → UnitTriangle)
    (covered : Covers 1 config) (packet : PacketConditions config) :
    ∀ p : Fin 177, True → ∃ owner, Common.allowed p owner = true ∧ Owns config owner p := by
  intro p _
  by_cases hc : Common.allowed p 6 = false
  · obtain ⟨owner, hlt, hp⟩ := packet.outerCoverage p hc
    exact ⟨owner, Common.outer_allowed p owner hlt, hp⟩
  · obtain ⟨owner, hp⟩ := Set.mem_iUnion.mp (covered (all_points_in_hexagon p))
    refine ⟨owner, ?_, hp⟩
    by_cases hlt : owner.val < 6
    · exact Common.outer_allowed p owner hlt
    · have heq : owner = 6 := by apply Fin.ext; omega
      subst owner
      exact Bool.eq_true_of_not_eq_false hc

end HexagonCover.NBand.M8300_8500.Semantics
