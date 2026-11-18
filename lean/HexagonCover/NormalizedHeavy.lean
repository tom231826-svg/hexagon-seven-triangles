import HexagonCover.GlobalMinimum
import HexagonCover.HeavyScale
import HexagonCover.HeavyTransport
import HexagonCover.ReachEquiv

/-! Normalize the same actual configuration so its unique heavy outer piece is
role5 and its longer actual reach goes along edge5. No orientation restriction
is imposed on any individual triangle. -/
namespace HexagonCover.NormalizedHeavy
open HexagonCover.Configuration QSymmetry ReachBudget ReachEquiv
noncomputable section

structure Normalized (config : Fin 7 → UnitTriangle) : Prop where
  cover : StrictCover config
  heavy5 : heavy cover 5
  long_right : a cover 5 ≤ b cover 5

theorem normalizer : ∀j : Fin 6, ∀flip : Bool, ∃n : Fin 6,
    (dihedral n flip).roles j.castSucc=5 ∧
    (dihedral n flip).roles (j-1).castSucc=(if flip then 0 else 4) ∧
    (dihedral n flip).roles (j+1).castSucc=(if flip then 4 else 0) := by
  decide

theorem exists_normalized {config : Fin 7 → UnitTriangle} (h : StrictCover config) :
    ∃action : Action, Normalized (action.transform config) := by
  obtain ⟨j,hj,_,_,_⟩ := GlobalMinimum.exists_unique_heavy h
  by_cases hab : a h j ≤ b h j
  · obtain ⟨n,h0,hm,hp⟩ := normalizer j false
    let action := dihedral n false
    have ha := left_left action h j 5 h0 hm
    have hb := right_right action h j 5 h0 hp
    refine ⟨action,⟨strictCover action h,?_,?_⟩⟩
    · change 1 ≤ a (strictCover action h) 5+b (strictCover action h) 5
      rw [←ha,←hb]
      exact hj
    · rw [←ha,←hb]
      exact hab
  · obtain ⟨n,h0,hm,hp⟩ := normalizer j true
    let action := dihedral n true
    have ha := left_right action h j 5 h0 hm
    have hb := right_left action h j 5 h0 hp
    refine ⟨action,⟨strictCover action h,?_,?_⟩⟩
    · change 1 ≤ a (strictCover action h) 5+b (strictCover action h) 5
      rw [←ha,←hb]
      change 1 ≤ a h j+b h j at hj
      linarith
    · rw [←ha,←hb]
      exact le_of_not_ge hab

def M {config : Fin 7 → UnitTriangle} (h : Normalized config) : ℝ := b h.cover 5

theorem max_eq_M {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    max (a h.cover 5) (b h.cover 5)=M h := max_eq_right h.long_right

theorem structure_bounds {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    (∀i,1-M h ≤ min (a h.cover i) (b h.cover i)) ∧
    (∀i,heavy h.cover i → i=5) ∧
    1 < a h.cover 5+b h.cover 5 ∧
    (2:ℝ)/3 < M h ∧ M h < 1 ∧
    Symmetry.NonIntruding (1/2) (config 5) := by
  obtain ⟨j,hj,hl,hq,hu⟩ := GlobalMinimum.exists_unique_heavy h.cover
  have he : j=5 := (hu 5 h.heavy5).symm
  subst j
  have hsum := GlobalMinimum.heavy_sum_gt_one h.cover 5 h.heavy5 hl hu
  have hscale := HeavyScale.two_thirds h.cover 5 h.heavy5 hl hu
  have hni := HeavyTransport.actual_heavy_nonintruding h.cover 5 h.heavy5
    (by rw [HeavyTransport.q_eq_sqrt_div_three]; exact hq)
  rw [max_eq_M h] at hl hscale
  exact ⟨hl,hu,hsum,hscale,(rightReach h.cover 5).lt_one,hni⟩

theorem edge5_no_gap {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    ¬BoundaryGaps.gap h.cover 5 := by
  have hl := (structure_bounds h).1 (0:Fin 6)
  have ha := hl.trans (min_le_left _ _)
  change 1-M h ≤ a h.cover 0 at ha
  change ¬(b h.cover 5+a h.cover (5+1) < 1)
  have he : (5:Fin 6)+1=0 := by decide
  rw [he]
  change ¬(M h+a h.cover 0 < 1)
  linarith

end
end HexagonCover.NormalizedHeavy
