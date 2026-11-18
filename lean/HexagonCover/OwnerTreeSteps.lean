import HexagonCover.OwnerTree

/-! Proof-producing assembly for the exact same OwnerTree Boolean checker.
Explicit intermediate paths avoid repeatedly reducing nested function updates. -/
namespace HexagonCover.OwnerTree

theorem branch_checked [DecidableEq Point]
    (inDomain : Point → Bool) (allowed : Point → Owner → Bool)
    (leafCheck : Owner → List Point → Certificate → Bool)
    (point : Point) (children : Owner → Tree Point Certificate) (path : Path Point)
    (domain : inDomain point = true)
    (each : ∀ owner, allowed point owner = true →
      check inDomain allowed leafCheck (children owner) (push path owner point) = true) :
    check inDomain allowed leafCheck (.branch point children) path = true := by
  exact Bool.and_eq_true_iff.mpr ⟨domain, decide_eq_true each⟩

theorem check_path_eq [DecidableEq Point]
    (inDomain : Point → Bool) (allowed : Point → Owner → Bool)
    (leafCheck : Owner → List Point → Certificate → Bool)
    (tree : Tree Point Certificate) {path other : Path Point}
    (equal : path = other) (accepted : check inDomain allowed leafCheck tree other = true) :
    check inDomain allowed leafCheck tree path = true := by
  simpa only [equal] using accepted

end HexagonCover.OwnerTree
