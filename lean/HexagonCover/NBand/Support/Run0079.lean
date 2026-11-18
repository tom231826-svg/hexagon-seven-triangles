import HexagonCover.SupportInteger

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.Support.Run0079
open DistanceLeaf SupportWitness SupportWitnessSymmetry

namespace C003865
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-415200,0),(0,96000)⟩,⟨(-2076000,0),(0,2076000)⟩,⟨(-1384000,0),(0,2076000)⟩,⟨(-1038000,0),(0,1730000)⟩,⟨(-3570201,0),(0,581799)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 4152000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003865

namespace C003866
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-2000,0),(0,10000)⟩,⟨(-12000,0),(0,12000)⟩,⟨(-12000,0),(0,4000)⟩,⟨(-8000,0),(0,12000)⟩,⟨(-20637,0),(0,3363)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003866

namespace C003867
def integerPoints : Fin 8 → SupportInteger.Point := ![⟨(-2698800,0),(0,624000)⟩,⟨(-1032291,0),(-1376388,0)⟩,⟨(-1376388,0),(-1032291,0)⟩,⟨(-661725,0),(-1588140,0)⟩,⟨(0,0),(-1720485,0)⟩,⟨(0,0),(0,8996000)⟩,⟨(19836180,0),(0,-1248000)⟩,⟨(15743000,0),(0,2249000)⟩]
def points : Fin 8 → ExactPoint := fun i => SupportInteger.decode 26988000 (integerPoints i)

def pair_0_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 7 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 7 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 7 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 7 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 7 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 7 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 7 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def pair_1_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 7 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 7 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 7 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 7 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 7 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 7 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 7 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_1_7_1_selection (by decide +kernel)

def pair_1_7 : Bool → Selection 7 :=
  fun b => if b then e_1_7_1_selection else e_1_7_0_selection

def pair_2_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 7 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 7 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 7 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 7 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 7 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_2_7_1_selection (by decide +kernel)

def pair_2_7 : Bool → Selection 7 :=
  fun b => if b then e_2_7_1_selection else e_2_7_0_selection

def pair_3_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 7 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 7 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 7 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_3_7_1_selection (by decide +kernel)

def pair_3_7 : Bool → Selection 7 :=
  fun b => if b then e_3_7_1_selection else e_3_7_0_selection

def pair_4_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 7 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 7 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_4_7_1_selection (by decide +kernel)

def pair_4_7 : Bool → Selection 7 :=
  fun b => if b then e_4_7_1_selection else e_4_7_0_selection

def pair_5_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 7 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 7 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 7 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_5_7_1_selection (by decide +kernel)

def pair_5_7 : Bool → Selection 7 :=
  fun b => if b then e_5_7_1_selection else e_5_7_0_selection

def pair_6_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_6_7_0_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_6_7_1_selection (by decide +kernel)

def pair_6_7 : Bool → Selection 7 :=
  fun b => if b then e_6_7_1_selection else e_6_7_0_selection

def pair_7_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_5 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_6 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_7 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 7 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6,pair_0_7], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6,pair_1_7], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6,pair_2_7], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6,pair_3_7], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6,pair_4_7], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6,pair_5_7], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6,pair_6_7], ![pair_7_0,pair_7_1,pair_7_2,pair_7_3,pair_7_4,pair_7_5,pair_7_6,pair_7_7]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
      · cases negative
        · exact e_0_6_0
        · exact e_0_6_1
      · cases negative
        · exact e_0_7_0
        · exact e_0_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
      · cases negative
        · exact e_1_6_0
        · exact e_1_6_1
      · cases negative
        · exact e_1_7_0
        · exact e_1_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
      · cases negative
        · exact e_2_6_0
        · exact e_2_6_1
      · cases negative
        · exact e_2_7_0
        · exact e_2_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
      · cases negative
        · exact e_3_6_0
        · exact e_3_6_1
      · cases negative
        · exact e_3_7_0
        · exact e_3_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
      · cases negative
        · exact e_4_6_0
        · exact e_4_6_1
      · cases negative
        · exact e_4_7_0
        · exact e_4_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_5_6_0
        · exact e_5_6_1
      · cases negative
        · exact e_5_7_0
        · exact e_5_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_6_7_0
        · exact e_6_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 7, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003867

namespace C003868
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-207600,0),(0,48000)⟩,⟨(-105876,0),(-79407,0)⟩,⟨(0,0),(0,692000)⟩,⟨(346000,0),(0,-346000)⟩,⟨(1211000,0),(0,173000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2076000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003868

namespace C003869
def integerPoints : Fin 8 → SupportInteger.Point := ![⟨(-2698800,0),(0,624000)⟩,⟨(-4498000,0),(0,4498000)⟩,⟨(-1032291,0),(-1376388,0)⟩,⟨(-1376388,0),(-1032291,0)⟩,⟨(-661725,0),(-1588140,0)⟩,⟨(0,0),(-1720485,0)⟩,⟨(19836180,0),(0,-1248000)⟩,⟨(15743000,0),(0,2249000)⟩]
def points : Fin 8 → ExactPoint := fun i => SupportInteger.decode 26988000 (integerPoints i)

def pair_0_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 7 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 7 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 7 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 7 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 7 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 7 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 7 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def pair_1_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 7 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 7 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 7 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 7 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 7 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_1_7_1_selection (by decide +kernel)

def pair_1_7 : Bool → Selection 7 :=
  fun b => if b then e_1_7_1_selection else e_1_7_0_selection

def pair_2_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 7 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 7 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 7 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 7 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_2_7_1_selection (by decide +kernel)

def pair_2_7 : Bool → Selection 7 :=
  fun b => if b then e_2_7_1_selection else e_2_7_0_selection

def pair_3_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 7 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 7 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 7 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 7 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_3_7_1_selection (by decide +kernel)

def pair_3_7 : Bool → Selection 7 :=
  fun b => if b then e_3_7_1_selection else e_3_7_0_selection

def pair_4_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 7 := ![⟨7, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 7 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 7 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_4_7_1_selection (by decide +kernel)

def pair_4_7 : Bool → Selection 7 :=
  fun b => if b then e_4_7_1_selection else e_4_7_0_selection

def pair_5_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 7 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_5_7_1_selection (by decide +kernel)

def pair_5_7 : Bool → Selection 7 :=
  fun b => if b then e_5_7_1_selection else e_5_7_0_selection

def pair_6_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_6_7_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 26988000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_6_7_1_selection (by decide +kernel)

def pair_6_7 : Bool → Selection 7 :=
  fun b => if b then e_6_7_1_selection else e_6_7_0_selection

def pair_7_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_2 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_3 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_4 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_5 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_6 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_7 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 7 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6,pair_0_7], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6,pair_1_7], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6,pair_2_7], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6,pair_3_7], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6,pair_4_7], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6,pair_5_7], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6,pair_6_7], ![pair_7_0,pair_7_1,pair_7_2,pair_7_3,pair_7_4,pair_7_5,pair_7_6,pair_7_7]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
      · cases negative
        · exact e_0_6_0
        · exact e_0_6_1
      · cases negative
        · exact e_0_7_0
        · exact e_0_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
      · cases negative
        · exact e_1_6_0
        · exact e_1_6_1
      · cases negative
        · exact e_1_7_0
        · exact e_1_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
      · cases negative
        · exact e_2_6_0
        · exact e_2_6_1
      · cases negative
        · exact e_2_7_0
        · exact e_2_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
      · cases negative
        · exact e_3_6_0
        · exact e_3_6_1
      · cases negative
        · exact e_3_7_0
        · exact e_3_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
      · cases negative
        · exact e_4_6_0
        · exact e_4_6_1
      · cases negative
        · exact e_4_7_0
        · exact e_4_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_5_6_0
        · exact e_5_6_1
      · cases negative
        · exact e_5_7_0
        · exact e_5_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_6_7_0
        · exact e_6_7_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 7, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003869

namespace C003870
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-207600,0),(0,48000)⟩,⟨(-346000,0),(0,346000)⟩,⟨(-105876,0),(-79407,0)⟩,⟨(692000,0),(0,-692000)⟩,⟨(1211000,0),(0,173000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2076000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003870

namespace C003871
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(2076000,0),(0,-2076000)⟩,⟨(2076000,0),(0,-692000)⟩,⟨(3051720,0),(0,-192000)⟩,⟨(3570201,0),(0,-581799)⟩,⟨(1453200,0),(0,-2076000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 4152000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003871

namespace C003872
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-800,0),(0,0)⟩,⟨(0,0),(153,0)⟩,⟨(1200,0),(0,-400)⟩,⟨(1400,0),(0,200)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 2400 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003872

namespace C003873
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-539760,0),(0,124800)⟩,⟨(-899600,0),(0,-899600)⟩,⟨(-132345,0),(317628,0)⟩,⟨(0,0),(344097,0)⟩,⟨(3967236,0),(0,-249600)⟩,⟨(3148600,0),(0,449800)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 5397600 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 5 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def pair_2_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 5 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def pair_3_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 5 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def pair_4_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 5 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def pair_5_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 5 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 5, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003873

namespace C003874
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(2076000,0),(0,-2076000)⟩,⟨(1384000,0),(0,-2076000)⟩,⟨(1038000,0),(0,-1730000)⟩,⟨(3051720,0),(0,-192000)⟩,⟨(3570201,0),(0,-581799)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 4152000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003874

namespace C003875
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-539760,0),(0,124800)⟩,⟨(-899600,0),(0,-899600)⟩,⟨(-132345,0),(317628,0)⟩,⟨(0,0),(344097,0)⟩,⟨(1349400,0),(0,-2249000)⟩,⟨(3148600,0),(0,449800)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 5397600 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 5 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def pair_2_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 5 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def pair_3_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 5 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def pair_4_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 5397600 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 5 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def pair_5_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 5 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 5, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003875

namespace C003876
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-207600,0),(0,48000)⟩,⟨(-519000,0),(0,519000)⟩,⟨(-105876,0),(-79407,0)⟩,⟨(519000,0),(0,-519000)⟩,⟨(1211000,0),(0,173000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2076000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003876

namespace C003877
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4152000,0),(0,0)⟩,⟨(-2076000,0),(0,0)⟩,⟨(-2076000,0),(0,692000)⟩,⟨(-3806000,0),(0,346000)⟩,⟨(-2657799,0),(0,-1494201)⟩,⟨(-2532720,0),(0,-1608000)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 4152000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 5 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def pair_2_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 5 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def pair_3_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 5 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def pair_4_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 5 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def pair_5_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 5 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 5, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003877

namespace C003878
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-346000,0),(0,-346000)⟩,⟨(-397900,0),(0,-294100)⟩,⟨(-110720,0),(0,0)⟩,⟨(-422120,0),(0,-268000)⟩,⟨(152067,0),(0,-346000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 692000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003878

namespace C003879
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-51900,0),(0,-51900)⟩,⟨(-25950,0),(0,-25950)⟩,⟨(-59685,0),(0,-44115)⟩,⟨(-63318,0),(0,-40200)⟩,⟨(34600,0),(0,-51900)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003879

namespace C003880
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-346000,0),(0,-346000)⟩,⟨(-55360,0),(0,-55360)⟩,⟨(-397900,0),(0,-294100)⟩,⟨(-422120,0),(0,-268000)⟩,⟨(152067,0),(0,-346000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 692000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 692000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003880

namespace C003881
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-24000,0),(0,0)⟩,⟨(-12000,0),(0,4000)⟩,⟨(-4000,0),(0,0)⟩,⟨(-22000,0),(0,2000)⟩,⟨(-15363,0),(0,-8637)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003881

namespace C003882
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-1038000,0),(0,-1038000)⟩,⟨(-346000,0),(0,0)⟩,⟨(-1193700,0),(0,-882300)⟩,⟨(-1266360,0),(0,-804000)⟩,⟨(456201,0),(0,-1038000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2076000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003882

namespace C003883
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-5200,0),(0,0)⟩,⟨(-2496,0),(0,-2496)⟩,⟨(-765,0),(1836,0)⟩,⟨(0,0),(1989,0)⟩,⟨(20800,0),(0,-5200)⟩,⟨(18200,0),(0,2600)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 31200 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 5 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def pair_2_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 5 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def pair_3_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 5 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def pair_4_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 31200 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 5 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def pair_5_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 5 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 5, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003883

namespace C003884
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(2076000,0),(0,-2076000)⟩,⟨(2076000,0),(0,-692000)⟩,⟨(1384000,0),(0,-2076000)⟩,⟨(3051720,0),(0,-192000)⟩,⟨(3570201,0),(0,-581799)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 4152000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 4152000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003884

namespace C003885
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-800,0),(0,0)⟩,⟨(-192,0),(0,-192)⟩,⟨(0,0),(153,0)⟩,⟨(1200,0),(0,-400)⟩,⟨(1400,0),(0,200)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2400 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003885

namespace C003886
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-24000,0),(0,0)⟩,⟨(-8000,0),(0,-4000)⟩,⟨(-22000,0),(0,2000)⟩,⟨(-16000,0),(0,4000)⟩,⟨(-15363,0),(0,-8637)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003886

namespace C003887
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-24000,0),(0,0)⟩,⟨(-22000,0),(0,2000)⟩,⟨(-16000,0),(0,4000)⟩,⟨(-3840,0),(0,0)⟩,⟨(-15363,0),(0,-8637)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003887

namespace C003888
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-24000,0),(0,0)⟩,⟨(-22000,0),(0,2000)⟩,⟨(-16000,0),(0,4000)⟩,⟨(-10000,0),(0,-6000)⟩,⟨(-15363,0),(0,-8637)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003888

namespace C003889
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-24000,0),(0,0)⟩,⟨(-12000,0),(0,-8000)⟩,⟨(-22000,0),(0,2000)⟩,⟨(-16000,0),(0,4000)⟩,⟨(-15363,0),(0,-8637)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003889

namespace C003890
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-24000,0),(0,0)⟩,⟨(-8000,0),(0,0)⟩,⟨(-22000,0),(0,2000)⟩,⟨(-16000,0),(0,4000)⟩,⟨(-15363,0),(0,-8637)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 24000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 24000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003890

namespace C003891
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-138400,0),(0,0)⟩,⟨(-24912,0),(0,-26400)⟩,⟨(0,0),(26469,0)⟩,⟨(207600,0),(0,-69200)⟩,⟨(242200,0),(0,34600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 415200 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 415200 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003891

namespace C003892
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(60000,0),(0,-60000)⟩,⟨(40000,0),(0,0)⟩,⟨(104889,0),(0,-15111)⟩,⟨(44400,0),(0,-60000)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003892

namespace C003893
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(20000,0),(0,-20000)⟩,⟨(20000,0),(0,0)⟩,⟨(34963,0),(0,-5037)⟩,⟨(14800,0),(0,-20000)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 40000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003893

namespace C003894
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-20000,0),(0,0)⟩,⟨(-20000,0),(0,20000)⟩,⟨(-34963,0),(0,5037)⟩,⟨(-14800,0),(0,20000)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 40000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003894

namespace C003895
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-10000,0),(0,0)⟩,⟨(0,0),(-1131,0)⟩,⟨(0,0),(1131,0)⟩,⟨(10000,0),(0,0)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 20000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003895

namespace C003896
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-120000,0),(0,0)⟩,⟨(-60000,0),(0,0)⟩,⟨(-40000,0),(0,-40000)⟩,⟨(-112200,0),(0,7800)⟩,⟨(-75111,0),(0,-44889)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003896

namespace C003897
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-120000,0),(0,0)⟩,⟨(-60000,0),(0,0)⟩,⟨(-112200,0),(0,7800)⟩,⟨(-80000,0),(0,20000)⟩,⟨(-75111,0),(0,-44889)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003897

namespace C003898
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-40000,0),(0,0)⟩,⟨(-10000,0),(0,-10000)⟩,⟨(-37400,0),(0,2600)⟩,⟨(-25037,0),(0,-14963)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 40000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 40000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003898

namespace C003899
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-30000,0),(0,-30000)⟩,⟨(-15000,0),(0,-15000)⟩,⟨(-33900,0),(0,-26100)⟩,⟨(-35000,0),(0,-15000)⟩,⟨(14889,0),(0,-30000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003899

namespace C003900
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-10000,0),(0,50000)⟩,⟨(-60000,0),(0,60000)⟩,⟨(-80000,0),(0,20000)⟩,⟨(-104889,0),(0,15111)⟩,⟨(-44400,0),(0,60000)⟩,⟨(-50000,0),(0,30000)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 5 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def pair_2_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 5 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def pair_3_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 5 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def pair_4_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 5 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def pair_5_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 5 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 5, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003900

namespace C003901
def integerPoints : Fin 9 → SupportInteger.Point := ![⟨(-25000,0),(0,125000)⟩,⟨(-16965,0),(0,0)⟩,⟨(-13572,0),(-10179,0)⟩,⟨(-15660,0),(-6525,0)⟩,⟨(-10179,0),(-13572,0)⟩,⟨(-6525,0),(-15660,0)⟩,⟨(0,0),(-16965,0)⟩,⟨(150000,0),(0,0)⟩,⟨(175000,0),(0,25000)⟩]
def points : Fin 9 → ExactPoint := fun i => SupportInteger.decode 300000 (integerPoints i)

def pair_0_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 8 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 8 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 8 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 8 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 8 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 8 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 8 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def e_0_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_0_8_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_0_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_0_8_0_selection (by decide +kernel)

def e_0_8_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_0_8_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_0_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_0_8_1_selection (by decide +kernel)

def pair_0_8 : Bool → Selection 8 :=
  fun b => if b then e_0_8_1_selection else e_0_8_0_selection

def pair_1_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 8 := ![⟨3, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 8 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 8 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 8 := ![⟨3, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 8 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 8 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 8 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨7, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 8 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_1_7_1_selection (by decide +kernel)

def pair_1_7 : Bool → Selection 8 :=
  fun b => if b then e_1_7_1_selection else e_1_7_0_selection

def e_1_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_1_8_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_1_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_1_8_0_selection (by decide +kernel)

def e_1_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_1_8_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_1_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_1_8_1_selection (by decide +kernel)

def pair_1_8 : Bool → Selection 8 :=
  fun b => if b then e_1_8_1_selection else e_1_8_0_selection

def pair_2_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 8 := ![⟨2, by decide⟩,⟨7, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 8 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 8 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 8 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨7, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 8 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 8 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_2_7_1_selection (by decide +kernel)

def pair_2_7 : Bool → Selection 8 :=
  fun b => if b then e_2_7_1_selection else e_2_7_0_selection

def e_2_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_2_8_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_2_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_2_8_0_selection (by decide +kernel)

def e_2_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_2_8_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_2_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_2_8_1_selection (by decide +kernel)

def pair_2_8 : Bool → Selection 8 :=
  fun b => if b then e_2_8_1_selection else e_2_8_0_selection

def pair_3_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 8 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 8 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 8 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 8 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_3_7_1_selection (by decide +kernel)

def pair_3_7 : Bool → Selection 8 :=
  fun b => if b then e_3_7_1_selection else e_3_7_0_selection

def e_3_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_3_8_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_3_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_3_8_0_selection (by decide +kernel)

def e_3_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_3_8_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_3_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_3_8_1_selection (by decide +kernel)

def pair_3_8 : Bool → Selection 8 :=
  fun b => if b then e_3_8_1_selection else e_3_8_0_selection

def pair_4_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 8 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨7, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 8 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 8 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_4_7_1_selection (by decide +kernel)

def pair_4_7 : Bool → Selection 8 :=
  fun b => if b then e_4_7_1_selection else e_4_7_0_selection

def e_4_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_4_8_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_4_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_4_8_0_selection (by decide +kernel)

def e_4_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_4_8_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_4_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_4_8_1_selection (by decide +kernel)

def pair_4_8 : Bool → Selection 8 :=
  fun b => if b then e_4_8_1_selection else e_4_8_0_selection

def pair_5_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨7, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 8 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 8 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_5_7_1_selection (by decide +kernel)

def pair_5_7 : Bool → Selection 8 :=
  fun b => if b then e_5_7_1_selection else e_5_7_0_selection

def e_5_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_5_8_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_5_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_5_8_0_selection (by decide +kernel)

def e_5_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_5_8_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_5_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_5_8_1_selection (by decide +kernel)

def pair_5_8 : Bool → Selection 8 :=
  fun b => if b then e_5_8_1_selection else e_5_8_0_selection

def pair_6_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_6_7_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 8 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_6_7_1_selection (by decide +kernel)

def pair_6_7 : Bool → Selection 8 :=
  fun b => if b then e_6_7_1_selection else e_6_7_0_selection

def e_6_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_6_8_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_6_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_6_8_0_selection (by decide +kernel)

def e_6_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_6_8_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_6_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_6_8_1_selection (by decide +kernel)

def pair_6_8 : Bool → Selection 8 :=
  fun b => if b then e_6_8_1_selection else e_6_8_0_selection

def pair_7_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_6 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_7 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_7_8_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨8, by decide⟩]
theorem e_7_8_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_7_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_7_8_0_selection (by decide +kernel)

def e_7_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_7_8_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_7_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_7_8_1_selection (by decide +kernel)

def pair_7_8 : Bool → Selection 8 :=
  fun b => if b then e_7_8_1_selection else e_7_8_0_selection

def pair_8_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_6 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_7 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_8 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 8 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6,pair_0_7,pair_0_8], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6,pair_1_7,pair_1_8], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6,pair_2_7,pair_2_8], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6,pair_3_7,pair_3_8], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6,pair_4_7,pair_4_8], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6,pair_5_7,pair_5_8], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6,pair_6_7,pair_6_8], ![pair_7_0,pair_7_1,pair_7_2,pair_7_3,pair_7_4,pair_7_5,pair_7_6,pair_7_7,pair_7_8], ![pair_8_0,pair_8_1,pair_8_2,pair_8_3,pair_8_4,pair_8_5,pair_8_6,pair_8_7,pair_8_8]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
      · cases negative
        · exact e_0_6_0
        · exact e_0_6_1
      · cases negative
        · exact e_0_7_0
        · exact e_0_7_1
      · cases negative
        · exact e_0_8_0
        · exact e_0_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
      · cases negative
        · exact e_1_6_0
        · exact e_1_6_1
      · cases negative
        · exact e_1_7_0
        · exact e_1_7_1
      · cases negative
        · exact e_1_8_0
        · exact e_1_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
      · cases negative
        · exact e_2_6_0
        · exact e_2_6_1
      · cases negative
        · exact e_2_7_0
        · exact e_2_7_1
      · cases negative
        · exact e_2_8_0
        · exact e_2_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
      · cases negative
        · exact e_3_6_0
        · exact e_3_6_1
      · cases negative
        · exact e_3_7_0
        · exact e_3_7_1
      · cases negative
        · exact e_3_8_0
        · exact e_3_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
      · cases negative
        · exact e_4_6_0
        · exact e_4_6_1
      · cases negative
        · exact e_4_7_0
        · exact e_4_7_1
      · cases negative
        · exact e_4_8_0
        · exact e_4_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_5_6_0
        · exact e_5_6_1
      · cases negative
        · exact e_5_7_0
        · exact e_5_7_1
      · cases negative
        · exact e_5_8_0
        · exact e_5_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_6_7_0
        · exact e_6_7_1
      · cases negative
        · exact e_6_8_0
        · exact e_6_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_7_8_0
        · exact e_7_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 8, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003901

namespace C003902
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-30000,0),(0,-30000)⟩,⟨(-20000,0),(0,-20000)⟩,⟨(-33900,0),(0,-26100)⟩,⟨(14889,0),(0,-30000)⟩,⟨(25000,0),(0,-25000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003902

namespace C003903
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-120000,0),(0,0)⟩,⟨(-20000,0),(0,-20000)⟩,⟨(-112200,0),(0,7800)⟩,⟨(-75111,0),(0,-44889)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 3 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def pair_2_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 3 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def pair_3_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 3 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 3, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003903

namespace C003904
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-30000,0),(0,-30000)⟩,⟨(-10000,0),(0,-10000)⟩,⟨(-33900,0),(0,-26100)⟩,⟨(-25000,0),(0,-5000)⟩,⟨(14889,0),(0,-30000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003904

namespace C003905
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-120000,0),(0,0)⟩,⟨(-60000,0),(0,20000)⟩,⟨(-112200,0),(0,7800)⟩,⟨(-75111,0),(0,-44889)⟩,⟨(-50000,0),(0,-10000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003905

namespace C003906
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,60000)⟩,⟨(-60000,0),(0,20000)⟩,⟨(-104889,0),(0,15111)⟩,⟨(-44400,0),(0,60000)⟩,⟨(0,0),(0,40000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003906

namespace C003907
def integerPoints : Fin 9 → SupportInteger.Point := ![⟨(-16965,0),(0,0)⟩,⟨(-13572,0),(-10179,0)⟩,⟨(-15660,0),(-6525,0)⟩,⟨(-10179,0),(-13572,0)⟩,⟨(-6525,0),(-15660,0)⟩,⟨(0,0),(-16965,0)⟩,⟨(0,0),(0,100000)⟩,⟨(150000,0),(0,0)⟩,⟨(200000,0),(0,50000)⟩]
def points : Fin 9 → ExactPoint := fun i => SupportInteger.decode 300000 (integerPoints i)

def pair_0_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 8 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 8 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 8 := ![⟨2, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 8 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 8 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 8 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 8 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨7, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 8 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def e_0_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_0_8_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_0_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_0_8_0_selection (by decide +kernel)

def e_0_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_0_8_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_0_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_0_8_1_selection (by decide +kernel)

def pair_0_8 : Bool → Selection 8 :=
  fun b => if b then e_0_8_1_selection else e_0_8_0_selection

def pair_1_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 8 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 8 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 8 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 8 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 8 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 8 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 8 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_1_7_1_selection (by decide +kernel)

def pair_1_7 : Bool → Selection 8 :=
  fun b => if b then e_1_7_1_selection else e_1_7_0_selection

def e_1_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_1_8_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_1_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_1_8_0_selection (by decide +kernel)

def e_1_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_1_8_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_1_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_1_8_1_selection (by decide +kernel)

def pair_1_8 : Bool → Selection 8 :=
  fun b => if b then e_1_8_1_selection else e_1_8_0_selection

def pair_2_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 8 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 8 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 8 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 8 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 8 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_2_7_1_selection (by decide +kernel)

def pair_2_7 : Bool → Selection 8 :=
  fun b => if b then e_2_7_1_selection else e_2_7_0_selection

def e_2_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_2_8_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_2_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_2_8_0_selection (by decide +kernel)

def e_2_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_2_8_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_2_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_2_8_1_selection (by decide +kernel)

def pair_2_8 : Bool → Selection 8 :=
  fun b => if b then e_2_8_1_selection else e_2_8_0_selection

def pair_3_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 8 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 8 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨7, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 8 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 8 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_3_7_1_selection (by decide +kernel)

def pair_3_7 : Bool → Selection 8 :=
  fun b => if b then e_3_7_1_selection else e_3_7_0_selection

def e_3_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_3_8_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_3_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_3_8_0_selection (by decide +kernel)

def e_3_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_3_8_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_3_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_3_8_1_selection (by decide +kernel)

def pair_3_8 : Bool → Selection 8 :=
  fun b => if b then e_3_8_1_selection else e_3_8_0_selection

def pair_4_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨7, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 8 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 8 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_4_7_1_selection (by decide +kernel)

def pair_4_7 : Bool → Selection 8 :=
  fun b => if b then e_4_7_1_selection else e_4_7_0_selection

def e_4_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_4_8_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_4_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_4_8_0_selection (by decide +kernel)

def e_4_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_4_8_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_4_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_4_8_1_selection (by decide +kernel)

def pair_4_8 : Bool → Selection 8 :=
  fun b => if b then e_4_8_1_selection else e_4_8_0_selection

def pair_5_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 8 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 8 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 8 := ![⟨5, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_5_7_1_selection (by decide +kernel)

def pair_5_7 : Bool → Selection 8 :=
  fun b => if b then e_5_7_1_selection else e_5_7_0_selection

def e_5_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_5_8_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_5_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_5_8_0_selection (by decide +kernel)

def e_5_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨8, by decide⟩,⟨0, by decide⟩]
theorem e_5_8_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_5_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_5_8_1_selection (by decide +kernel)

def pair_5_8 : Bool → Selection 8 :=
  fun b => if b then e_5_8_1_selection else e_5_8_0_selection

def pair_6_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_6_7_0_selection : Selection 8 := ![⟨8, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 8 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_6_7_1_selection (by decide +kernel)

def pair_6_7 : Bool → Selection 8 :=
  fun b => if b then e_6_7_1_selection else e_6_7_0_selection

def e_6_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_6_8_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_6_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_6_8_0_selection (by decide +kernel)

def e_6_8_1_selection : Selection 8 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨6, by decide⟩]
theorem e_6_8_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_6_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_6_8_1_selection (by decide +kernel)

def pair_6_8 : Bool → Selection 8 :=
  fun b => if b then e_6_8_1_selection else e_6_8_0_selection

def pair_7_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_6 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_7 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_7_8_0_selection : Selection 8 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨8, by decide⟩]
theorem e_7_8_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_7_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_7_8_0_selection (by decide +kernel)

def e_7_8_1_selection : Selection 8 := ![⟨7, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_7_8_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_7_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_7_8_1_selection (by decide +kernel)

def pair_7_8 : Bool → Selection 8 :=
  fun b => if b then e_7_8_1_selection else e_7_8_0_selection

def pair_8_0 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_1 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_2 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_3 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_4 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_5 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_6 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_7 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_8 : Bool → Selection 8 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 8 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6,pair_0_7,pair_0_8], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6,pair_1_7,pair_1_8], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6,pair_2_7,pair_2_8], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6,pair_3_7,pair_3_8], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6,pair_4_7,pair_4_8], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6,pair_5_7,pair_5_8], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6,pair_6_7,pair_6_8], ![pair_7_0,pair_7_1,pair_7_2,pair_7_3,pair_7_4,pair_7_5,pair_7_6,pair_7_7,pair_7_8], ![pair_8_0,pair_8_1,pair_8_2,pair_8_3,pair_8_4,pair_8_5,pair_8_6,pair_8_7,pair_8_8]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
      · cases negative
        · exact e_0_6_0
        · exact e_0_6_1
      · cases negative
        · exact e_0_7_0
        · exact e_0_7_1
      · cases negative
        · exact e_0_8_0
        · exact e_0_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
      · cases negative
        · exact e_1_6_0
        · exact e_1_6_1
      · cases negative
        · exact e_1_7_0
        · exact e_1_7_1
      · cases negative
        · exact e_1_8_0
        · exact e_1_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
      · cases negative
        · exact e_2_6_0
        · exact e_2_6_1
      · cases negative
        · exact e_2_7_0
        · exact e_2_7_1
      · cases negative
        · exact e_2_8_0
        · exact e_2_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
      · cases negative
        · exact e_3_6_0
        · exact e_3_6_1
      · cases negative
        · exact e_3_7_0
        · exact e_3_7_1
      · cases negative
        · exact e_3_8_0
        · exact e_3_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
      · cases negative
        · exact e_4_6_0
        · exact e_4_6_1
      · cases negative
        · exact e_4_7_0
        · exact e_4_7_1
      · cases negative
        · exact e_4_8_0
        · exact e_4_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_5_6_0
        · exact e_5_6_1
      · cases negative
        · exact e_5_7_0
        · exact e_5_7_1
      · cases negative
        · exact e_5_8_0
        · exact e_5_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_6_7_0
        · exact e_6_7_1
      · cases negative
        · exact e_6_8_0
        · exact e_6_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_7_8_0
        · exact e_7_8_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 8, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003907

namespace C003908
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-14889,0),(0,30000)⟩,⟨(0,0),(0,20000)⟩,⟨(30000,0),(0,30000)⟩,⟨(33900,0),(0,26100)⟩,⟨(35000,0),(0,15000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003908

namespace C003909
def integerPoints : Fin 10 → SupportInteger.Point := ![⟨(-16965,0),(0,0)⟩,⟨(-13572,0),(-10179,0)⟩,⟨(-13572,0),(10179,0)⟩,⟨(-15660,0),(-6525,0)⟩,⟨(-15660,0),(6525,0)⟩,⟨(-10179,0),(-13572,0)⟩,⟨(-10179,0),(13572,0)⟩,⟨(200000,0),(0,50000)⟩,⟨(125000,0),(0,-75000)⟩,⟨(175000,0),(0,75000)⟩]
def points : Fin 10 → ExactPoint := fun i => SupportInteger.decode 300000 (integerPoints i)

def pair_0_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 9 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 9 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 9 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 9 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨6, by decide⟩,⟨8, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 9 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 9 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 9 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 9 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 9 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨1, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 9 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 9 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def e_0_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_0_8_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_0_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_0_8_0_selection (by decide +kernel)

def e_0_8_1_selection : Selection 9 := ![⟨5, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_0_8_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_0_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_0_8_1_selection (by decide +kernel)

def pair_0_8 : Bool → Selection 9 :=
  fun b => if b then e_0_8_1_selection else e_0_8_0_selection

def e_0_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_9_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_0_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_0_9_0_selection (by decide +kernel)

def e_0_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_0_9_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_0_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_0_9_1_selection (by decide +kernel)

def pair_0_9 : Bool → Selection 9 :=
  fun b => if b then e_0_9_1_selection else e_0_9_0_selection

def pair_1_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨8, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 9 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 9 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 9 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨6, by decide⟩,⟨8, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 9 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 9 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 9 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨8, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 9 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_1_7_1_selection (by decide +kernel)

def pair_1_7 : Bool → Selection 9 :=
  fun b => if b then e_1_7_1_selection else e_1_7_0_selection

def e_1_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_1_8_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_1_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_1_8_0_selection (by decide +kernel)

def e_1_8_1_selection : Selection 9 := ![⟨5, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_1_8_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_1_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_1_8_1_selection (by decide +kernel)

def pair_1_8 : Bool → Selection 9 :=
  fun b => if b then e_1_8_1_selection else e_1_8_0_selection

def e_1_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_1_9_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_1_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_1_9_0_selection (by decide +kernel)

def e_1_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_1_9_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_1_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_1_9_1_selection (by decide +kernel)

def pair_1_9 : Bool → Selection 9 :=
  fun b => if b then e_1_9_1_selection else e_1_9_0_selection

def pair_2_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨8, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 9 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 9 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 9 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨6, by decide⟩,⟨8, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 9 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 9 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 9 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_2_7_1_selection (by decide +kernel)

def pair_2_7 : Bool → Selection 9 :=
  fun b => if b then e_2_7_1_selection else e_2_7_0_selection

def e_2_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_2_8_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_2_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_2_8_0_selection (by decide +kernel)

def e_2_8_1_selection : Selection 9 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_2_8_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_2_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_2_8_1_selection (by decide +kernel)

def pair_2_8 : Bool → Selection 9 :=
  fun b => if b then e_2_8_1_selection else e_2_8_0_selection

def e_2_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_2_9_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_2_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_2_9_0_selection (by decide +kernel)

def e_2_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_2_9_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_2_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_2_9_1_selection (by decide +kernel)

def pair_2_9 : Bool → Selection 9 :=
  fun b => if b then e_2_9_1_selection else e_2_9_0_selection

def pair_3_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨8, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 9 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 9 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 9 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 9 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨1, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 9 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_3_7_1_selection (by decide +kernel)

def pair_3_7 : Bool → Selection 9 :=
  fun b => if b then e_3_7_1_selection else e_3_7_0_selection

def e_3_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_3_8_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_3_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_3_8_0_selection (by decide +kernel)

def e_3_8_1_selection : Selection 9 := ![⟨5, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_3_8_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_3_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_3_8_1_selection (by decide +kernel)

def pair_3_8 : Bool → Selection 9 :=
  fun b => if b then e_3_8_1_selection else e_3_8_0_selection

def e_3_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_3_9_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_3_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_3_9_0_selection (by decide +kernel)

def e_3_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_3_9_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_3_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_3_9_1_selection (by decide +kernel)

def pair_3_9 : Bool → Selection 9 :=
  fun b => if b then e_3_9_1_selection else e_3_9_0_selection

def pair_4_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 9 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 9 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 9 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨3, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 9 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_4_7_1_selection (by decide +kernel)

def pair_4_7 : Bool → Selection 9 :=
  fun b => if b then e_4_7_1_selection else e_4_7_0_selection

def e_4_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_4_8_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_4_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_4_8_0_selection (by decide +kernel)

def e_4_8_1_selection : Selection 9 := ![⟨5, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_4_8_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_4_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_4_8_1_selection (by decide +kernel)

def pair_4_8 : Bool → Selection 9 :=
  fun b => if b then e_4_8_1_selection else e_4_8_0_selection

def e_4_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_4_9_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_4_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_4_9_0_selection (by decide +kernel)

def e_4_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_4_9_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_4_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_4_9_1_selection (by decide +kernel)

def pair_4_9 : Bool → Selection 9 :=
  fun b => if b then e_4_9_1_selection else e_4_9_0_selection

def pair_5_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨8, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 9 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_5_7_1_selection (by decide +kernel)

def pair_5_7 : Bool → Selection 9 :=
  fun b => if b then e_5_7_1_selection else e_5_7_0_selection

def e_5_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_5_8_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_5_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_5_8_0_selection (by decide +kernel)

def e_5_8_1_selection : Selection 9 := ![⟨5, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_5_8_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_5_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_5_8_1_selection (by decide +kernel)

def pair_5_8 : Bool → Selection 9 :=
  fun b => if b then e_5_8_1_selection else e_5_8_0_selection

def e_5_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_5_9_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_5_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_5_9_0_selection (by decide +kernel)

def e_5_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_5_9_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_5_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_5_9_1_selection (by decide +kernel)

def pair_5_9 : Bool → Selection 9 :=
  fun b => if b then e_5_9_1_selection else e_5_9_0_selection

def pair_6_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_6_7_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨5, by decide⟩,⟨7, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_6_7_1_selection (by decide +kernel)

def pair_6_7 : Bool → Selection 9 :=
  fun b => if b then e_6_7_1_selection else e_6_7_0_selection

def e_6_8_0_selection : Selection 9 := ![⟨9, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_6_8_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_6_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_6_8_0_selection (by decide +kernel)

def e_6_8_1_selection : Selection 9 := ![⟨1, by decide⟩,⟨7, by decide⟩,⟨9, by decide⟩]
theorem e_6_8_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_6_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_6_8_1_selection (by decide +kernel)

def pair_6_8 : Bool → Selection 9 :=
  fun b => if b then e_6_8_1_selection else e_6_8_0_selection

def e_6_9_0_selection : Selection 9 := ![⟨6, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_6_9_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_6_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_6_9_0_selection (by decide +kernel)

def e_6_9_1_selection : Selection 9 := ![⟨8, by decide⟩,⟨9, by decide⟩,⟨0, by decide⟩]
theorem e_6_9_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_6_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_6_9_1_selection (by decide +kernel)

def pair_6_9 : Bool → Selection 9 :=
  fun b => if b then e_6_9_1_selection else e_6_9_0_selection

def pair_7_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_4 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_5 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_6 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_7 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_7_8_0_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨1, by decide⟩]
theorem e_7_8_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_7_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_7_8_0_selection (by decide +kernel)

def e_7_8_1_selection : Selection 9 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_7_8_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_7_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_7_8_1_selection (by decide +kernel)

def pair_7_8 : Bool → Selection 9 :=
  fun b => if b then e_7_8_1_selection else e_7_8_0_selection

def e_7_9_0_selection : Selection 9 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_7_9_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_7_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_7_9_0_selection (by decide +kernel)

def e_7_9_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_7_9_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_7_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_7_9_1_selection (by decide +kernel)

def pair_7_9 : Bool → Selection 9 :=
  fun b => if b then e_7_9_1_selection else e_7_9_0_selection

def pair_8_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_4 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_5 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_6 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_7 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_8 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_8_9_0_selection : Selection 9 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨9, by decide⟩]
theorem e_8_9_0 : eventCheck points (points ⟨8, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_8_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨8, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_8_9_0_selection (by decide +kernel)

def e_8_9_1_selection : Selection 9 := ![⟨7, by decide⟩,⟨9, by decide⟩,⟨5, by decide⟩]
theorem e_8_9_1 : eventCheck points (points ⟨8, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_8_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨8, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_8_9_1_selection (by decide +kernel)

def pair_8_9 : Bool → Selection 9 :=
  fun b => if b then e_8_9_1_selection else e_8_9_0_selection

def pair_9_0 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_1 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_2 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_3 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_4 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_5 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_6 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_7 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_8 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_9 : Bool → Selection 9 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 9 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6,pair_0_7,pair_0_8,pair_0_9], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6,pair_1_7,pair_1_8,pair_1_9], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6,pair_2_7,pair_2_8,pair_2_9], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6,pair_3_7,pair_3_8,pair_3_9], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6,pair_4_7,pair_4_8,pair_4_9], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6,pair_5_7,pair_5_8,pair_5_9], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6,pair_6_7,pair_6_8,pair_6_9], ![pair_7_0,pair_7_1,pair_7_2,pair_7_3,pair_7_4,pair_7_5,pair_7_6,pair_7_7,pair_7_8,pair_7_9], ![pair_8_0,pair_8_1,pair_8_2,pair_8_3,pair_8_4,pair_8_5,pair_8_6,pair_8_7,pair_8_8,pair_8_9], ![pair_9_0,pair_9_1,pair_9_2,pair_9_3,pair_9_4,pair_9_5,pair_9_6,pair_9_7,pair_9_8,pair_9_9]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
      · cases negative
        · exact e_0_6_0
        · exact e_0_6_1
      · cases negative
        · exact e_0_7_0
        · exact e_0_7_1
      · cases negative
        · exact e_0_8_0
        · exact e_0_8_1
      · cases negative
        · exact e_0_9_0
        · exact e_0_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
      · cases negative
        · exact e_1_6_0
        · exact e_1_6_1
      · cases negative
        · exact e_1_7_0
        · exact e_1_7_1
      · cases negative
        · exact e_1_8_0
        · exact e_1_8_1
      · cases negative
        · exact e_1_9_0
        · exact e_1_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
      · cases negative
        · exact e_2_6_0
        · exact e_2_6_1
      · cases negative
        · exact e_2_7_0
        · exact e_2_7_1
      · cases negative
        · exact e_2_8_0
        · exact e_2_8_1
      · cases negative
        · exact e_2_9_0
        · exact e_2_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
      · cases negative
        · exact e_3_6_0
        · exact e_3_6_1
      · cases negative
        · exact e_3_7_0
        · exact e_3_7_1
      · cases negative
        · exact e_3_8_0
        · exact e_3_8_1
      · cases negative
        · exact e_3_9_0
        · exact e_3_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
      · cases negative
        · exact e_4_6_0
        · exact e_4_6_1
      · cases negative
        · exact e_4_7_0
        · exact e_4_7_1
      · cases negative
        · exact e_4_8_0
        · exact e_4_8_1
      · cases negative
        · exact e_4_9_0
        · exact e_4_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_5_6_0
        · exact e_5_6_1
      · cases negative
        · exact e_5_7_0
        · exact e_5_7_1
      · cases negative
        · exact e_5_8_0
        · exact e_5_8_1
      · cases negative
        · exact e_5_9_0
        · exact e_5_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_6_7_0
        · exact e_6_7_1
      · cases negative
        · exact e_6_8_0
        · exact e_6_8_1
      · cases negative
        · exact e_6_9_0
        · exact e_6_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_7_8_0
        · exact e_7_8_1
      · cases negative
        · exact e_7_9_0
        · exact e_7_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_8_9_0
        · exact e_8_9_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 9, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003909

namespace C003910
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(60000,0),(0,-60000)⟩,⟨(80000,0),(0,0)⟩,⟨(104889,0),(0,-15111)⟩,⟨(44400,0),(0,-60000)⟩,⟨(50000,0),(0,-30000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003910

namespace C003911
def integerPoints : Fin 11 → SupportInteger.Point := ![⟨(-16965,0),(0,0)⟩,⟨(-13572,0),(-10179,0)⟩,⟨(-15660,0),(-6525,0)⟩,⟨(-15660,0),(6525,0)⟩,⟨(-10179,0),(-13572,0)⟩,⟨(-6525,0),(-15660,0)⟩,⟨(0,0),(-16965,0)⟩,⟨(50000,0),(0,100000)⟩,⟨(200000,0),(0,0)⟩,⟨(200000,0),(0,50000)⟩,⟨(175000,0),(0,75000)⟩]
def points : Fin 11 → ExactPoint := fun i => SupportInteger.decode 300000 (integerPoints i)

def pair_0_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 10 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 10 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 10 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 10 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 10 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 10 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 10 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 10 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 10 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 10 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 10 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def e_0_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_0_8_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_0_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_0_8_0_selection (by decide +kernel)

def e_0_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_0_8_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_0_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_0_8_1_selection (by decide +kernel)

def pair_0_8 : Bool → Selection 10 :=
  fun b => if b then e_0_8_1_selection else e_0_8_0_selection

def e_0_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_0_9_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_0_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_0_9_0_selection (by decide +kernel)

def e_0_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_0_9_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_0_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_0_9_1_selection (by decide +kernel)

def pair_0_9 : Bool → Selection 10 :=
  fun b => if b then e_0_9_1_selection else e_0_9_0_selection

def e_0_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_0_10_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_0_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_0_10_0_selection (by decide +kernel)

def e_0_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_0_10_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_0_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_0_10_1_selection (by decide +kernel)

def pair_0_10 : Bool → Selection 10 :=
  fun b => if b then e_0_10_1_selection else e_0_10_0_selection

def pair_1_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 10 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 10 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 10 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 10 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 10 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 10 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 10 := ![⟨5, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 10 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_1_7_1_selection (by decide +kernel)

def pair_1_7 : Bool → Selection 10 :=
  fun b => if b then e_1_7_1_selection else e_1_7_0_selection

def e_1_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_1_8_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_1_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_1_8_0_selection (by decide +kernel)

def e_1_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨10, by decide⟩,⟨7, by decide⟩]
theorem e_1_8_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_1_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_1_8_1_selection (by decide +kernel)

def pair_1_8 : Bool → Selection 10 :=
  fun b => if b then e_1_8_1_selection else e_1_8_0_selection

def e_1_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_1_9_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_1_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_1_9_0_selection (by decide +kernel)

def e_1_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_1_9_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_1_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_1_9_1_selection (by decide +kernel)

def pair_1_9 : Bool → Selection 10 :=
  fun b => if b then e_1_9_1_selection else e_1_9_0_selection

def e_1_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_1_10_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_1_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_1_10_0_selection (by decide +kernel)

def e_1_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_1_10_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_1_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_1_10_1_selection (by decide +kernel)

def pair_1_10 : Bool → Selection 10 :=
  fun b => if b then e_1_10_1_selection else e_1_10_0_selection

def pair_2_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 10 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 10 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨7, by decide⟩,⟨8, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 10 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 10 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 10 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 10 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_2_7_1_selection (by decide +kernel)

def pair_2_7 : Bool → Selection 10 :=
  fun b => if b then e_2_7_1_selection else e_2_7_0_selection

def e_2_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_2_8_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_2_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_2_8_0_selection (by decide +kernel)

def e_2_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨10, by decide⟩,⟨7, by decide⟩]
theorem e_2_8_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_2_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_2_8_1_selection (by decide +kernel)

def pair_2_8 : Bool → Selection 10 :=
  fun b => if b then e_2_8_1_selection else e_2_8_0_selection

def e_2_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_2_9_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_2_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_2_9_0_selection (by decide +kernel)

def e_2_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_2_9_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_2_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_2_9_1_selection (by decide +kernel)

def pair_2_9 : Bool → Selection 10 :=
  fun b => if b then e_2_9_1_selection else e_2_9_0_selection

def e_2_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_2_10_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_2_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_2_10_0_selection (by decide +kernel)

def e_2_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_2_10_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_2_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_2_10_1_selection (by decide +kernel)

def pair_2_10 : Bool → Selection 10 :=
  fun b => if b then e_2_10_1_selection else e_2_10_0_selection

def pair_3_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 10 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 10 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 10 := ![⟨2, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 10 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 10 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_3_7_1_selection (by decide +kernel)

def pair_3_7 : Bool → Selection 10 :=
  fun b => if b then e_3_7_1_selection else e_3_7_0_selection

def e_3_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_3_8_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_3_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_3_8_0_selection (by decide +kernel)

def e_3_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_3_8_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_3_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_3_8_1_selection (by decide +kernel)

def pair_3_8 : Bool → Selection 10 :=
  fun b => if b then e_3_8_1_selection else e_3_8_0_selection

def e_3_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_3_9_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_3_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_3_9_0_selection (by decide +kernel)

def e_3_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_3_9_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_3_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_3_9_1_selection (by decide +kernel)

def pair_3_9 : Bool → Selection 10 :=
  fun b => if b then e_3_9_1_selection else e_3_9_0_selection

def e_3_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_3_10_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_3_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_3_10_0_selection (by decide +kernel)

def e_3_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_3_10_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_3_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_3_10_1_selection (by decide +kernel)

def pair_3_10 : Bool → Selection 10 :=
  fun b => if b then e_3_10_1_selection else e_3_10_0_selection

def pair_4_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 10 := ![⟨4, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 10 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 10 := ![⟨5, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 10 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_4_7_1_selection (by decide +kernel)

def pair_4_7 : Bool → Selection 10 :=
  fun b => if b then e_4_7_1_selection else e_4_7_0_selection

def e_4_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_4_8_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_4_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_4_8_0_selection (by decide +kernel)

def e_4_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨10, by decide⟩,⟨7, by decide⟩]
theorem e_4_8_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_4_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_4_8_1_selection (by decide +kernel)

def pair_4_8 : Bool → Selection 10 :=
  fun b => if b then e_4_8_1_selection else e_4_8_0_selection

def e_4_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_4_9_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_4_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_4_9_0_selection (by decide +kernel)

def e_4_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_4_9_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_4_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_4_9_1_selection (by decide +kernel)

def pair_4_9 : Bool → Selection 10 :=
  fun b => if b then e_4_9_1_selection else e_4_9_0_selection

def e_4_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_4_10_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_4_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_4_10_0_selection (by decide +kernel)

def e_4_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_4_10_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_4_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_4_10_1_selection (by decide +kernel)

def pair_4_10 : Bool → Selection 10 :=
  fun b => if b then e_4_10_1_selection else e_4_10_0_selection

def pair_5_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨2, by decide⟩,⟨8, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 10 := ![⟨5, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 10 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨1, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_5_7_1_selection (by decide +kernel)

def pair_5_7 : Bool → Selection 10 :=
  fun b => if b then e_5_7_1_selection else e_5_7_0_selection

def e_5_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_5_8_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_5_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_5_8_0_selection (by decide +kernel)

def e_5_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨10, by decide⟩,⟨7, by decide⟩]
theorem e_5_8_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_5_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_5_8_1_selection (by decide +kernel)

def pair_5_8 : Bool → Selection 10 :=
  fun b => if b then e_5_8_1_selection else e_5_8_0_selection

def e_5_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_5_9_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_5_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_5_9_0_selection (by decide +kernel)

def e_5_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_5_9_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_5_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_5_9_1_selection (by decide +kernel)

def pair_5_9 : Bool → Selection 10 :=
  fun b => if b then e_5_9_1_selection else e_5_9_0_selection

def e_5_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_5_10_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_5_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_5_10_0_selection (by decide +kernel)

def e_5_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_5_10_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_5_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_5_10_1_selection (by decide +kernel)

def pair_5_10 : Bool → Selection 10 :=
  fun b => if b then e_5_10_1_selection else e_5_10_0_selection

def pair_6_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_6_7_0_selection : Selection 10 := ![⟨3, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨4, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_6_7_1_selection (by decide +kernel)

def pair_6_7 : Bool → Selection 10 :=
  fun b => if b then e_6_7_1_selection else e_6_7_0_selection

def e_6_8_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨1, by decide⟩,⟨8, by decide⟩]
theorem e_6_8_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_6_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_6_8_0_selection (by decide +kernel)

def e_6_8_1_selection : Selection 10 := ![⟨6, by decide⟩,⟨10, by decide⟩,⟨7, by decide⟩]
theorem e_6_8_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_6_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_6_8_1_selection (by decide +kernel)

def pair_6_8 : Bool → Selection 10 :=
  fun b => if b then e_6_8_1_selection else e_6_8_0_selection

def e_6_9_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨4, by decide⟩,⟨8, by decide⟩]
theorem e_6_9_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_6_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_6_9_0_selection (by decide +kernel)

def e_6_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_6_9_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_6_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_6_9_1_selection (by decide +kernel)

def pair_6_9 : Bool → Selection 10 :=
  fun b => if b then e_6_9_1_selection else e_6_9_0_selection

def e_6_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨5, by decide⟩,⟨9, by decide⟩]
theorem e_6_10_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_6_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_6_10_0_selection (by decide +kernel)

def e_6_10_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨10, by decide⟩,⟨0, by decide⟩]
theorem e_6_10_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_6_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_6_10_1_selection (by decide +kernel)

def pair_6_10 : Bool → Selection 10 :=
  fun b => if b then e_6_10_1_selection else e_6_10_0_selection

def pair_7_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_5 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_6 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_7_7 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_7_8_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨3, by decide⟩,⟨8, by decide⟩]
theorem e_7_8_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ false e_7_8_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    false e_7_8_0_selection (by decide +kernel)

def e_7_8_1_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_7_8_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨8, by decide⟩)
    ⟨0, by decide⟩ true e_7_8_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨8, by decide⟩)
    true e_7_8_1_selection (by decide +kernel)

def pair_7_8 : Bool → Selection 10 :=
  fun b => if b then e_7_8_1_selection else e_7_8_0_selection

def e_7_9_0_selection : Selection 10 := ![⟨10, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_7_9_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_7_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_7_9_0_selection (by decide +kernel)

def e_7_9_1_selection : Selection 10 := ![⟨4, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_7_9_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_7_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_7_9_1_selection (by decide +kernel)

def pair_7_9 : Bool → Selection 10 :=
  fun b => if b then e_7_9_1_selection else e_7_9_0_selection

def e_7_10_0_selection : Selection 10 := ![⟨7, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩]
theorem e_7_10_0 : eventCheck points (points ⟨7, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_7_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_7_10_0_selection (by decide +kernel)

def e_7_10_1_selection : Selection 10 := ![⟨5, by decide⟩,⟨9, by decide⟩,⟨7, by decide⟩]
theorem e_7_10_1 : eventCheck points (points ⟨7, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_7_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨7, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_7_10_1_selection (by decide +kernel)

def pair_7_10 : Bool → Selection 10 :=
  fun b => if b then e_7_10_1_selection else e_7_10_0_selection

def pair_8_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_5 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_6 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_7 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_8_8 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_8_9_0_selection : Selection 10 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨10, by decide⟩]
theorem e_8_9_0 : eventCheck points (points ⟨8, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ false e_8_9_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨8, by decide⟩) (integerPoints ⟨9, by decide⟩)
    false e_8_9_0_selection (by decide +kernel)

def e_8_9_1_selection : Selection 10 := ![⟨8, by decide⟩,⟨7, by decide⟩,⟨4, by decide⟩]
theorem e_8_9_1 : eventCheck points (points ⟨8, by decide⟩) (points ⟨9, by decide⟩)
    ⟨0, by decide⟩ true e_8_9_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨8, by decide⟩) (integerPoints ⟨9, by decide⟩)
    true e_8_9_1_selection (by decide +kernel)

def pair_8_9 : Bool → Selection 10 :=
  fun b => if b then e_8_9_1_selection else e_8_9_0_selection

def e_8_10_0_selection : Selection 10 := ![⟨0, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_8_10_0 : eventCheck points (points ⟨8, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_8_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨8, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_8_10_0_selection (by decide +kernel)

def e_8_10_1_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨5, by decide⟩]
theorem e_8_10_1 : eventCheck points (points ⟨8, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_8_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨8, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_8_10_1_selection (by decide +kernel)

def pair_8_10 : Bool → Selection 10 :=
  fun b => if b then e_8_10_1_selection else e_8_10_0_selection

def pair_9_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_5 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_6 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_7 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_8 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_9_9 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_9_10_0_selection : Selection 10 := ![⟨1, by decide⟩,⟨8, by decide⟩,⟨7, by decide⟩]
theorem e_9_10_0 : eventCheck points (points ⟨9, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ false e_9_10_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨9, by decide⟩) (integerPoints ⟨10, by decide⟩)
    false e_9_10_0_selection (by decide +kernel)

def e_9_10_1_selection : Selection 10 := ![⟨9, by decide⟩,⟨7, by decide⟩,⟨6, by decide⟩]
theorem e_9_10_1 : eventCheck points (points ⟨9, by decide⟩) (points ⟨10, by decide⟩)
    ⟨0, by decide⟩ true e_9_10_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨9, by decide⟩) (integerPoints ⟨10, by decide⟩)
    true e_9_10_1_selection (by decide +kernel)

def pair_9_10 : Bool → Selection 10 :=
  fun b => if b then e_9_10_1_selection else e_9_10_0_selection

def pair_10_0 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_1 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_2 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_3 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_4 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_5 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_6 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_7 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_8 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_9 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_10_10 : Bool → Selection 10 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 10 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6,pair_0_7,pair_0_8,pair_0_9,pair_0_10], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6,pair_1_7,pair_1_8,pair_1_9,pair_1_10], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6,pair_2_7,pair_2_8,pair_2_9,pair_2_10], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6,pair_3_7,pair_3_8,pair_3_9,pair_3_10], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6,pair_4_7,pair_4_8,pair_4_9,pair_4_10], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6,pair_5_7,pair_5_8,pair_5_9,pair_5_10], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6,pair_6_7,pair_6_8,pair_6_9,pair_6_10], ![pair_7_0,pair_7_1,pair_7_2,pair_7_3,pair_7_4,pair_7_5,pair_7_6,pair_7_7,pair_7_8,pair_7_9,pair_7_10], ![pair_8_0,pair_8_1,pair_8_2,pair_8_3,pair_8_4,pair_8_5,pair_8_6,pair_8_7,pair_8_8,pair_8_9,pair_8_10], ![pair_9_0,pair_9_1,pair_9_2,pair_9_3,pair_9_4,pair_9_5,pair_9_6,pair_9_7,pair_9_8,pair_9_9,pair_9_10], ![pair_10_0,pair_10_1,pair_10_2,pair_10_3,pair_10_4,pair_10_5,pair_10_6,pair_10_7,pair_10_8,pair_10_9,pair_10_10]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
      · cases negative
        · exact e_0_5_0
        · exact e_0_5_1
      · cases negative
        · exact e_0_6_0
        · exact e_0_6_1
      · cases negative
        · exact e_0_7_0
        · exact e_0_7_1
      · cases negative
        · exact e_0_8_0
        · exact e_0_8_1
      · cases negative
        · exact e_0_9_0
        · exact e_0_9_1
      · cases negative
        · exact e_0_10_0
        · exact e_0_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
      · cases negative
        · exact e_1_5_0
        · exact e_1_5_1
      · cases negative
        · exact e_1_6_0
        · exact e_1_6_1
      · cases negative
        · exact e_1_7_0
        · exact e_1_7_1
      · cases negative
        · exact e_1_8_0
        · exact e_1_8_1
      · cases negative
        · exact e_1_9_0
        · exact e_1_9_1
      · cases negative
        · exact e_1_10_0
        · exact e_1_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
      · cases negative
        · exact e_2_5_0
        · exact e_2_5_1
      · cases negative
        · exact e_2_6_0
        · exact e_2_6_1
      · cases negative
        · exact e_2_7_0
        · exact e_2_7_1
      · cases negative
        · exact e_2_8_0
        · exact e_2_8_1
      · cases negative
        · exact e_2_9_0
        · exact e_2_9_1
      · cases negative
        · exact e_2_10_0
        · exact e_2_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
      · cases negative
        · exact e_3_5_0
        · exact e_3_5_1
      · cases negative
        · exact e_3_6_0
        · exact e_3_6_1
      · cases negative
        · exact e_3_7_0
        · exact e_3_7_1
      · cases negative
        · exact e_3_8_0
        · exact e_3_8_1
      · cases negative
        · exact e_3_9_0
        · exact e_3_9_1
      · cases negative
        · exact e_3_10_0
        · exact e_3_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_4_5_0
        · exact e_4_5_1
      · cases negative
        · exact e_4_6_0
        · exact e_4_6_1
      · cases negative
        · exact e_4_7_0
        · exact e_4_7_1
      · cases negative
        · exact e_4_8_0
        · exact e_4_8_1
      · cases negative
        · exact e_4_9_0
        · exact e_4_9_1
      · cases negative
        · exact e_4_10_0
        · exact e_4_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_5_6_0
        · exact e_5_6_1
      · cases negative
        · exact e_5_7_0
        · exact e_5_7_1
      · cases negative
        · exact e_5_8_0
        · exact e_5_8_1
      · cases negative
        · exact e_5_9_0
        · exact e_5_9_1
      · cases negative
        · exact e_5_10_0
        · exact e_5_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_6_7_0
        · exact e_6_7_1
      · cases negative
        · exact e_6_8_0
        · exact e_6_8_1
      · cases negative
        · exact e_6_9_0
        · exact e_6_9_1
      · cases negative
        · exact e_6_10_0
        · exact e_6_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_7_8_0
        · exact e_7_8_1
      · cases negative
        · exact e_7_9_0
        · exact e_7_9_1
      · cases negative
        · exact e_7_10_0
        · exact e_7_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_8_9_0
        · exact e_8_9_1
      · cases negative
        · exact e_8_10_0
        · exact e_8_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_9_10_0
        · exact e_9_10_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 10, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003911

namespace C003912
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-30000,0),(0,-30000)⟩,⟨(-20000,0),(0,-20000)⟩,⟨(-33900,0),(0,-26100)⟩,⟨(20000,0),(0,-20000)⟩,⟨(14889,0),(0,-30000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 4 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def pair_2_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 4 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def pair_3_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 4 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def pair_4_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 4 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4]]

theorem reduced_checked : ReducedChecked points selected where
  distinct := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide +kernel⟩
  events := by
    intro i j hij negative
    fin_cases i
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_0_1_0
        · exact e_0_1_1
      · cases negative
        · exact e_0_2_0
        · exact e_0_2_1
      · cases negative
        · exact e_0_3_0
        · exact e_0_3_1
      · cases negative
        · exact e_0_4_0
        · exact e_0_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_1_2_0
        · exact e_1_2_1
      · cases negative
        · exact e_1_3_0
        · exact e_1_3_1
      · cases negative
        · exact e_1_4_0
        · exact e_1_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_2_3_0
        · exact e_2_3_1
      · cases negative
        · exact e_2_4_0
        · exact e_2_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · cases negative
        · exact e_3_4_0
        · exact e_3_4_1
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 4, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C003912

end HexagonCover.NBand.Support.Run0079
