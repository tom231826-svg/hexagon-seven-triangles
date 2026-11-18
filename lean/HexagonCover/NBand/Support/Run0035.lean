import HexagonCover.SupportInteger

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.Support.Run0035
open DistanceLeaf SupportWitness SupportWitnessSymmetry

namespace C001688
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-30000,0),(0,10000)⟩,⟨(-10000,0),(0,0)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-51900,0),(0,8100)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

end C001688

namespace C001689
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-51900,0),(0,51900)⟩,⟨(-69200,0),(0,17300)⟩,⟨(-23874,0),(0,51900)⟩,⟨(-86500,0),(0,17300)⟩,⟨(8823,0),(0,32400)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

end C001689

namespace C001690
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-17300,0),(0,0)⟩,⟨(34600,0),(0,34600)⟩,⟨(8823,0),(0,32400)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

end C001690

namespace C001691
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-3750,0),(0,6250)⟩,⟨(-2622,0),(0,7500)⟩,⟨(7500,0),(0,7500)⟩,⟨(5000,0),(0,5000)⟩,⟨(9525,0),(0,5475)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 15000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

end C001691

namespace C001692
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-10380000,0),(0,0)⟩,⟨(-5190000,0),(0,1730000)⟩,⟨(-7122237,0),(0,-3257763)⟩,⟨(-8978700,0),(0,1401300)⟩,⟨(-1089900,0),(0,-1140000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 10380000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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

end C001692

namespace C001693
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-30000,0),(0,10000)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-51900,0),(0,8100)⟩,⟨(-8400,0),(0,8400)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

end C001693

namespace C001694
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-17300,0),(0,0)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(-14532,0),(0,14532)⟩,⟨(60550,0),(0,8650)⟩,⟨(42039,0),(0,-18600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

end C001694

namespace C001695
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-17300,0),(0,0)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(-14532,0),(0,14532)⟩,⟨(17300,0),(0,-34600)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

end C001695

namespace C001696
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-30000,0),(0,10000)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-51900,0),(0,8100)⟩,⟨(-16800,0),(0,0)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

end C001696

namespace C001697
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(10380000,0),(0,-10380000)⟩,⟨(4774800,0),(0,-10380000)⟩,⟨(15570000,0),(0,-1730000)⟩,⟨(16258713,0),(0,-4501287)⟩,⟨(8407800,0),(0,-3720000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 20760000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 20760000 (by decide) integerPoints
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

end C001697

namespace C001698
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-17300,0),(0,0)⟩,⟨(8650,0),(0,43250)⟩,⟨(56571,0),(0,20100)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

end C001698

namespace C001699
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-1,0),(0,-1)⟩,⟨(-1,0),(0,5)⟩,⟨(-2,0),(0,0)⟩,⟨(1,0),(0,5)⟩,⟨(7,0),(0,1)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
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

end C001699

namespace C001700
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25,0),(0,75)⟩,⟨(-25,0),(0,125)⟩,⟨(-150,0),(0,150)⟩,⟨(-69,0),(0,150)⟩,⟨(-250,0),(0,50)⟩,⟨(-42,0),(0,42)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

end C001700

namespace C001701
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25,0),(0,-25)⟩,⟨(-50,0),(0,0)⟩,⟨(-42,0),(0,42)⟩,⟨(25,0),(0,125)⟩,⟨(175,0),(0,25)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

end C001701

namespace C001702
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-8650,0),(0,25950)⟩,⟨(-17300,0),(0,0)⟩,⟨(60550,0),(0,8650)⟩,⟨(42039,0),(0,-18600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

end C001702

namespace C001703
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-4325,0),(0,12975)⟩,⟨(-8650,0),(0,0)⟩,⟨(30621,0),(0,150)⟩,⟨(30275,0),(0,4325)⟩,⟨(7266,0),(0,-7266)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C001703

namespace C001704
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-12975,0),(0,4325)⟩,⟨(-14532,0),(0,0)⟩,⟨(21625,0),(0,-4325)⟩,⟨(30621,0),(0,150)⟩,⟨(30275,0),(0,4325)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C001704

namespace C001705
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(69200,0),(0,0)⟩,⟨(43250,0),(0,-8650)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

end C001705

namespace C001706
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(30000,0),(0,-30000)⟩,⟨(40000,0),(0,0)⟩,⟨(13800,0),(0,-30000)⟩,⟨(50000,0),(0,-10000)⟩,⟨(51540,0),(0,-8409)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

end C001706

namespace C001707
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(150,0),(0,-150)⟩,⟨(200,0),(0,0)⟩,⟨(69,0),(0,-150)⟩,⟨(258,0),(0,-42)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

end C001707

namespace C001708
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,-8650)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

end C001708

namespace C001709
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(51900,0),(0,-17300)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

end C001709

namespace C001710
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(43250,0),(0,-25950)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

end C001710

namespace C001711
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(34600,0),(0,-34600)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

end C001711

namespace C001712
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-10899,0),(0,-11400)⟩,⟨(25950,0),(0,-43250)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

end C001712

namespace C001713
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25,0),(0,125)⟩,⟨(-150,0),(0,150)⟩,⟨(-69,0),(0,150)⟩,⟨(-250,0),(0,50)⟩,⟨(-42,0),(0,42)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

end C001713

namespace C001714
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-25950,0),(0,8650)⟩,⟨(-14532,0),(0,14532)⟩,⟨(60550,0),(0,8650)⟩,⟨(42039,0),(0,-18600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

end C001714

namespace C001715
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-25950,0),(0,8650)⟩,⟨(8823,0),(0,32400)⟩,⟨(61242,0),(0,300)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

end C001715

namespace C001716
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-12975,0),(0,4325)⟩,⟨(-14532,0),(0,0)⟩,⟨(-7266,0),(0,7266)⟩,⟨(30621,0),(0,150)⟩,⟨(30275,0),(0,4325)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C001716

namespace C001717
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-30000,0),(0,-30000)⟩,⟨(-20000,0),(0,0)⟩,⟨(-38100,0),(0,-21900)⟩,⟨(-16800,0),(0,0)⟩,⟨(3981,0),(0,-30000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

end C001717

namespace C001718
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25,0),(0,-25)⟩,⟨(-100,0),(0,0)⟩,⟨(-75,0),(0,25)⟩,⟨(-42,0),(0,42)⟩,⟨(175,0),(0,25)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

end C001718

namespace C001719
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-12975,0),(0,4325)⟩,⟨(-7266,0),(0,7266)⟩,⟨(30621,0),(0,150)⟩,⟨(30275,0),(0,4325)⟩,⟨(7266,0),(0,7266)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C001719

namespace C001720
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-12975,0),(0,4325)⟩,⟨(-7266,0),(0,7266)⟩,⟨(25950,0),(0,8650)⟩,⟨(30621,0),(0,150)⟩,⟨(30275,0),(0,4325)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C001720

namespace C001721
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-12975,0),(0,12975)⟩,⟨(-8650,0),(0,0)⟩,⟨(30621,0),(0,150)⟩,⟨(30275,0),(0,4325)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C001721

namespace C001722
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-43250,0),(0,8650)⟩,⟨(60550,0),(0,8650)⟩,⟨(42039,0),(0,-18600)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

end C001722

namespace C001723
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-10000,0),(0,0)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-51900,0),(0,8100)⟩,⟨(-40000,0),(0,10000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

end C001723

namespace C001724
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-10380000,0),(0,0)⟩,⟨(-7122237,0),(0,-3257763)⟩,⟨(-8978700,0),(0,1401300)⟩,⟨(-6920000,0),(0,1730000)⟩,⟨(-1089900,0),(0,-1140000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 10380000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380000 (by decide) integerPoints
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

end C001724

namespace C001725
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-51900,0),(0,8100)⟩,⟨(-40000,0),(0,10000)⟩,⟨(-8400,0),(0,8400)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

end C001725

namespace C001726
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-51900,0),(0,8100)⟩,⟨(-40000,0),(0,10000)⟩,⟨(-16800,0),(0,0)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

end C001726

namespace C001727
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-17300,0),(0,0)⟩,⟨(8823,0),(0,32400)⟩,⟨(43250,0),(0,-8650)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

end C001727

namespace C001728
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-51900,0),(0,51900)⟩,⟨(-23874,0),(0,51900)⟩,⟨(-86500,0),(0,17300)⟩,⟨(-14532,0),(0,14532)⟩,⟨(8823,0),(0,32400)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

end C001728

namespace C001729
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-5000,0),(0,5000)⟩,⟨(-2622,0),(0,7500)⟩,⟨(1250,0),(0,3750)⟩,⟨(7500,0),(0,7500)⟩,⟨(9525,0),(0,5475)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 15000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

end C001729

namespace C001730
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-51900,0),(0,51900)⟩,⟨(-23874,0),(0,51900)⟩,⟨(-86500,0),(0,17300)⟩,⟨(8650,0),(0,25950)⟩,⟨(8823,0),(0,32400)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

end C001730

namespace C001731
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25,0),(0,-25)⟩,⟨(-50,0),(0,0)⟩,⟨(-42,0),(0,42)⟩,⟨(25,0),(0,75)⟩,⟨(125,0),(0,-25)⟩,⟨(175,0),(0,25)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
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

end C001731

namespace C001732
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-3750,0),(0,6250)⟩,⟨(-2622,0),(0,7500)⟩,⟨(7500,0),(0,7500)⟩,⟨(7500,0),(0,3300)⟩,⟨(9525,0),(0,5475)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 15000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

end C001732

namespace C001733
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-3750,0),(0,6250)⟩,⟨(-2622,0),(0,7500)⟩,⟨(1250,0),(0,3750)⟩,⟨(7500,0),(0,7500)⟩,⟨(9525,0),(0,5475)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 15000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 15000 (by decide) integerPoints
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

end C001733

namespace C001734
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-10000,0),(0,0)⟩,⟨(-41169,0),(0,-18831)⟩,⟨(-50000,0),(0,10000)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
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

end C001734

namespace C001735
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-30000,0),(0,30000)⟩,⟨(-49749,0),(0,10251)⟩,⟨(-13800,0),(0,30000)⟩,⟨(-35000,0),(0,5000)⟩,⟨(-8400,0),(0,8400)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

end C001735

end HexagonCover.NBand.Support.Run0035
