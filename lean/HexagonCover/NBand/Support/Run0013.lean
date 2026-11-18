import HexagonCover.SupportInteger

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.Support.Run0013
open DistanceLeaf SupportWitness SupportWitnessSymmetry

namespace C000626
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-300,0),(0,-300)⟩,⟨(-300,0),(0,-100)⟩,⟨(-393,0),(0,-207)⟩,⟨(-192,0),(0,0)⟩,⟨(100,0),(0,-300)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 600 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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

end C000626

namespace C000627
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-300,0),(0,-300)⟩,⟨(-393,0),(0,-207)⟩,⟨(-350,0),(0,-150)⟩,⟨(-192,0),(0,0)⟩,⟨(100,0),(0,-300)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 600 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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

end C000627

namespace C000628
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-2400,0),(0,0)⟩,⟨(-800,0),(0,400)⟩,⟨(-1635,0),(0,-765)⟩,⟨(-2028,0),(0,372)⟩,⟨(-384,0),(0,384)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2400 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

end C000628

namespace C000629
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-103800,0),(0,0)⟩,⟨(-34600,0),(0,17300)⟩,⟨(-20760,0),(0,4500)⟩,⟨(-87711,0),(0,16089)⟩,⟨(-69200,0),(0,-34600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
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

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

end C000629

namespace C000630
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25,0),(0,75)⟩,⟨(-150,0),(0,150)⟩,⟨(-50,0),(0,150)⟩,⟨(-48,0),(0,48)⟩,⟨(-250,0),(0,50)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

end C000630

namespace C000631
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-2400,0),(0,0)⟩,⟨(-400,0),(0,400)⟩,⟨(-1635,0),(0,-765)⟩,⟨(-2028,0),(0,372)⟩,⟨(-384,0),(0,384)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2400 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2400 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

end C000631

namespace C000632
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-865,0),(0,2595)⟩,⟨(-5190,0),(0,5190)⟩,⟨(-2076,0),(0,450)⟩,⟨(-1730,0),(0,5190)⟩,⟨(-8650,0),(0,1730)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 10380 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

end C000632

namespace C000633
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-138400,0),(0,0)⟩,⟨(-27680,0),(0,6000)⟩,⟨(-94285,0),(0,-44115)⟩,⟨(-116948,0),(0,21452)⟩,⟨(-22144,0),(0,22144)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 138400 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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

end C000633

namespace C000634
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-25950,0),(0,25950)⟩,⟨(-10380,0),(0,2250)⟩,⟨(-9861,0),(0,25950)⟩,⟨(-43250,0),(0,8650)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
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

end C000634

namespace C000635
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-138400,0),(0,0)⟩,⟨(-27680,0),(0,6000)⟩,⟨(-94285,0),(0,-44115)⟩,⟨(-116948,0),(0,21452)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 138400 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 138400 (by decide) integerPoints
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

end C000635

namespace C000636
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-865000,0),(0,-865000)⟩,⟨(-346000,0),(0,75000)⟩,⟨(-1133150,0),(0,-596850)⟩,⟨(158641,0),(0,-865000)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 1730000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 1730000 (by decide) integerPoints
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

end C000636

namespace C000637
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-11245000,0),(0,-11245000)⟩,⟨(-26988000,0),(0,5850000)⟩,⟨(-22490000,0),(0,0)⟩,⟨(33735000,0),(0,56225000)⟩,⟨(5550705,0),(-13321692,0)⟩,⟨(78715000,0),(0,11245000)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 134940000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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

end C000637

namespace C000638
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-11245000,0),(0,-11245000)⟩,⟨(-26988000,0),(0,5850000)⟩,⟨(-22490000,0),(0,0)⟩,⟨(11245000,0),(0,56225000)⟩,⟨(5550705,0),(-13321692,0)⟩,⟨(78715000,0),(0,11245000)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 134940000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
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

end C000638

namespace C000639
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-7500,0),(0,12500)⟩,⟨(-4881,0),(0,15000)⟩,⟨(15000,0),(0,15000)⟩,⟨(19650,0),(0,10350)⟩,⟨(9600,0),(0,0)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 30000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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

end C000639

namespace C000640
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-7500,0),(0,12500)⟩,⟨(-4881,0),(0,15000)⟩,⟨(15000,0),(0,15000)⟩,⟨(19650,0),(0,10350)⟩,⟨(17500,0),(0,7500)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 30000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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

end C000640

namespace C000641
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-7500,0),(0,12500)⟩,⟨(-4881,0),(0,15000)⟩,⟨(15000,0),(0,15000)⟩,⟨(7500,0),(0,7500)⟩,⟨(19650,0),(0,10350)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 30000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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

end C000641

namespace C000642
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-865,0),(0,-865)⟩,⟨(-2076,0),(0,450)⟩,⟨(-1730,0),(0,0)⟩,⟨(2595,0),(0,-865)⟩,⟨(2595,0),(0,2595)⟩,⟨(6055,0),(0,865)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 10380 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

end C000642

namespace C000643
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-2500,0),(0,2500)⟩,⟨(-1627,0),(0,5000)⟩,⟨(5000,0),(0,5000)⟩,⟨(6550,0),(0,3450)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 10000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10000 (by decide) integerPoints
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

end C000643

namespace C000644
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-20000)⟩,⟨(60000,0),(0,-60000)⟩,⟨(22800,0),(0,-60000)⟩,⟨(90000,0),(0,-10000)⟩,⟨(91233,0),(0,-28767)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

end C000644

namespace C000645
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-865,0),(0,-865)⟩,⟨(-865,0),(0,865)⟩,⟨(-2076,0),(0,450)⟩,⟨(-1730,0),(0,0)⟩,⟨(7785,0),(0,-865)⟩,⟨(6055,0),(0,865)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 10380 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

end C000645

namespace C000646
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(600,0),(0,0)⟩,⟨(399,0),(0,201)⟩,⟨(507,0),(0,-93)⟩,⟨(450,0),(0,-50)⟩,⟨(250,0),(0,150)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 600 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 4 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def pair_1_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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

end C000646

namespace C000647
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-11245000,0),(0,-11245000)⟩,⟨(-11245000,0),(0,11245000)⟩,⟨(-26988000,0),(0,5850000)⟩,⟨(-22490000,0),(0,0)⟩,⟨(5550705,0),(-13321692,0)⟩,⟨(56225000,0),(0,33735000)⟩,⟨(78715000,0),(0,11245000)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 134940000 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 6 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def pair_2_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 6 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def pair_3_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 6 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def pair_4_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 6 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def pair_5_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 134940000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 6 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def pair_6_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 6 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6]]

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
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 6, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C000647

namespace C000648
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-20000)⟩,⟨(60000,0),(0,-60000)⟩,⟨(60000,0),(0,0)⟩,⟨(22800,0),(0,-60000)⟩,⟨(91233,0),(0,-28767)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

end C000648

namespace C000649
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-20000)⟩,⟨(60000,0),(0,-60000)⟩,⟨(22800,0),(0,-60000)⟩,⟨(91233,0),(0,-28767)⟩,⟨(50000,0),(0,-10000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

end C000649

namespace C000650
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-865,0),(0,-865)⟩,⟨(-865,0),(0,4325)⟩,⟨(-2076,0),(0,450)⟩,⟨(-1730,0),(0,0)⟩,⟨(5190,0),(0,0)⟩,⟨(6055,0),(0,865)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 10380 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

end C000650

namespace C000651
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-865,0),(0,-865)⟩,⟨(-2076,0),(0,450)⟩,⟨(-1730,0),(0,0)⟩,⟨(0,0),(0,3460)⟩,⟨(4325,0),(0,-865)⟩,⟨(6055,0),(0,865)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 10380 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

end C000651

namespace C000652
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-865,0),(0,-865)⟩,⟨(-2076,0),(0,450)⟩,⟨(-1730,0),(0,0)⟩,⟨(865,0),(0,2595)⟩,⟨(4325,0),(0,-865)⟩,⟨(6055,0),(0,865)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 10380 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 10380 (by decide) integerPoints
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

end C000652

namespace C000653
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-15000,0),(0,-15000)⟩,⟨(-19650,0),(0,-10350)⟩,⟨(5000,0),(0,-5000)⟩,⟨(2751,0),(0,-15000)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 30000 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 30000 (by decide) integerPoints
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

end C000653

namespace C000654
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-20000)⟩,⟨(60000,0),(0,-60000)⟩,⟨(22800,0),(0,-60000)⟩,⟨(91233,0),(0,-28767)⟩,⟨(70000,0),(0,-10000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 120000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 120000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

end C000654

namespace C000655
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-100,0),(0,300)⟩,⟨(300,0),(0,300)⟩,⟨(300,0),(0,100)⟩,⟨(393,0),(0,207)⟩,⟨(96,0),(0,96)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 600 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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

end C000655

namespace C000656
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(200,0),(0,0)⟩,⟨(133,0),(0,67)⟩,⟨(169,0),(0,-31)⟩,⟨(32,0),(0,32)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 200 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 3 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def pair_1_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 200 (by decide) integerPoints
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

end C000656

namespace C000657
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-150,0),(0,150)⟩,⟨(-57,0),(0,150)⟩,⟨(-250,0),(0,50)⟩,⟨(50,0),(0,50)⟩,⟨(48,0),(0,48)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 300 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

end C000657

namespace C000658
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(600,0),(0,0)⟩,⟨(100,0),(0,100)⟩,⟨(399,0),(0,201)⟩,⟨(507,0),(0,-93)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 600 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
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

end C000658

namespace C000659
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-17300,0),(0,51900)⟩,⟨(51900,0),(0,51900)⟩,⟨(17300,0),(0,17300)⟩,⟨(67989,0),(0,35811)⟩,⟨(58128,0),(0,15600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

end C000659

namespace C000660
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-17300,0),(0,51900)⟩,⟨(-11937,0),(0,12900)⟩,⟨(51900,0),(0,51900)⟩,⟨(51900,0),(0,17300)⟩,⟨(67989,0),(0,35811)⟩,⟨(60550,0),(0,25950)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

end C000660

namespace C000661
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-51900,0),(0,51900)⟩,⟨(-19722,0),(0,51900)⟩,⟨(-11937,0),(0,12900)⟩,⟨(-86500,0),(0,17300)⟩,⟨(16608,0),(0,16608)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

end C000661

namespace C000662
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-103800,0),(0,0)⟩,⟨(-87711,0),(0,16089)⟩,⟨(-69200,0),(0,-34600)⟩,⟨(-11937,0),(0,12900)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 3 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 3 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

end C000662

namespace C000663
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-17300)⟩,⟨(51900,0),(0,-51900)⟩,⟨(52419,0),(0,-12000)⟩,⟨(19722,0),(0,-51900)⟩,⟨(87192,0),(0,-16608)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

end C000663

namespace C000664
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-20760,0),(0,4500)⟩,⟨(-17300,0),(0,0)⟩,⟨(-11937,0),(0,12900)⟩,⟨(52419,0),(0,-12000)⟩,⟨(58128,0),(0,15600)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 6 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def pair_2_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 6 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def pair_3_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 6 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def pair_4_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 6 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def pair_5_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 6 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def pair_6_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 6 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6]]

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
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 6, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C000664

namespace C000665
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-5536,0),(0,-5536)⟩,⟨(17300,0),(0,-17300)⟩,⟨(17473,0),(0,-4000)⟩,⟨(6574,0),(0,-17300)⟩,⟨(29064,0),(0,-5536)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 34600 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 34600 (by decide) integerPoints
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

end C000665

namespace C000666
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-4325,0),(0,4325)⟩,⟨(-10380,0),(0,2250)⟩,⟨(-8304,0),(0,-8304)⟩,⟨(29064,0),(0,7800)⟩,⟨(21625,0),(0,-4325)⟩,⟨(30275,0),(0,4325)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_0_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
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

def e_2_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

end C000666

namespace C000667
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-4325,0),(0,4325)⟩,⟨(-10380,0),(0,2250)⟩,⟨(-16608,0),(0,0)⟩,⟨(29064,0),(0,7800)⟩,⟨(21625,0),(0,-4325)⟩,⟨(30275,0),(0,4325)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 6 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def pair_2_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 6 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def pair_3_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 6 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def pair_4_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 6 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def pair_5_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 6 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def pair_6_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 6 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6]]

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
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 6, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C000667

namespace C000668
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-103800,0),(0,0)⟩,⟨(-87711,0),(0,16089)⟩,⟨(-69200,0),(0,-34600)⟩,⟨(-11937,0),(0,12900)⟩,⟨(-16608,0),(0,16608)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

end C000668

namespace C000669
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-20760,0),(0,4500)⟩,⟨(-17300,0),(0,0)⟩,⟨(-16608,0),(0,16608)⟩,⟨(52419,0),(0,-12000)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

end C000669

namespace C000670
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-17300)⟩,⟨(51900,0),(0,-51900)⟩,⟨(52419,0),(0,-12000)⟩,⟨(19722,0),(0,-51900)⟩,⟨(86500,0),(0,-17300)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

end C000670

namespace C000671
def integerPoints : Fin 8 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-20760,0),(0,4500)⟩,⟨(-17300,0),(0,0)⟩,⟨(-11937,0),(0,12900)⟩,⟨(52419,0),(0,-12000)⟩,⟨(58128,0),(0,15600)⟩,⟨(16608,0),(0,-16608)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 8 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 7 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 7 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 7 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 7 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 7 := ![⟨7, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 7 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 7 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨7, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 7 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨3, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 7 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def e_0_7_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_0_7_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_0_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_0_7_0_selection (by decide +kernel)

def e_0_7_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_7_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_0_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨7, by decide⟩)
    true e_0_7_1_selection (by decide +kernel)

def pair_0_7 : Bool → Selection 7 :=
  fun b => if b then e_0_7_1_selection else e_0_7_0_selection

def pair_1_0 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 7 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 7 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 7 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 7 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨7, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 7 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 7 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 7 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def e_1_7_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_7_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_1_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_1_7_0_selection (by decide +kernel)

def e_1_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_7_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_1_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 7 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 7 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 7 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 7 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def e_2_7_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_7_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_2_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_2_7_0_selection (by decide +kernel)

def e_2_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_7_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_2_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 7 := ![⟨0, by decide⟩,⟨7, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 7 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 7 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 7 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 7 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def e_3_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_7_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_3_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_3_7_0_selection (by decide +kernel)

def e_3_7_1_selection : Selection 7 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_7_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_3_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 7 := ![⟨7, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 7 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 7 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def e_4_7_0_selection : Selection 7 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_7_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_4_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_4_7_0_selection (by decide +kernel)

def e_4_7_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_4_7_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_4_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_5_6_0_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 7 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def e_5_7_0_selection : Selection 7 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_5_7_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_5_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_5_7_0_selection (by decide +kernel)

def e_5_7_1_selection : Selection 7 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_5_7_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_5_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

def e_6_7_0_selection : Selection 7 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_6_7_0 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ false e_6_7_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨6, by decide⟩) (integerPoints ⟨7, by decide⟩)
    false e_6_7_0_selection (by decide +kernel)

def e_6_7_1_selection : Selection 7 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_6_7_1 : eventCheck points (points ⟨6, by decide⟩) (points ⟨7, by decide⟩)
    ⟨0, by decide⟩ true e_6_7_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
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

end C000671

namespace C000672
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-8650,0),(0,8650)⟩,⟨(-20760,0),(0,4500)⟩,⟨(-17300,0),(0,0)⟩,⟨(17300,0),(0,17300)⟩,⟨(52419,0),(0,-12000)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 6 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def pair_2_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 6 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def pair_3_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 6 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def pair_4_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 6 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def pair_5_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 6 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def pair_6_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 6 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6]]

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
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 6, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C000672

namespace C000673
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-8650,0),(0,8650)⟩,⟨(-20760,0),(0,4500)⟩,⟨(-17300,0),(0,0)⟩,⟨(52419,0),(0,-12000)⟩,⟨(16608,0),(0,16608)⟩,⟨(60550,0),(0,8650)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_1_6_1_selection (by decide +kernel)

def pair_1_6 : Bool → Selection 6 :=
  fun b => if b then e_1_6_1_selection else e_1_6_0_selection

def pair_2_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_2_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_2_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_2_6_1_selection (by decide +kernel)

def pair_2_6 : Bool → Selection 6 :=
  fun b => if b then e_2_6_1_selection else e_2_6_0_selection

def pair_3_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_3_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_3_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_3_6_1_selection (by decide +kernel)

def pair_3_6 : Bool → Selection 6 :=
  fun b => if b then e_3_6_1_selection else e_3_6_0_selection

def pair_4_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_4_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_4_5_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_4_6_1_selection (by decide +kernel)

def pair_4_6 : Bool → Selection 6 :=
  fun b => if b then e_4_6_1_selection else e_4_6_0_selection

def pair_5_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_5_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_5_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_5_6_1_selection (by decide +kernel)

def pair_5_6 : Bool → Selection 6 :=
  fun b => if b then e_5_6_1_selection else e_5_6_0_selection

def pair_6_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_2 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_3 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_4 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_5 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_6_6 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def selected : ReducedSelections 6 := ![![pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_0_6], ![pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_1_6], ![pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_2_6], ![pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_3_6], ![pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_4_6], ![pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5,pair_5_6], ![pair_6_0,pair_6_1,pair_6_2,pair_6_3,pair_6_4,pair_6_5,pair_6_6]]

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
    · fin_cases j
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij
      · norm_num [Fin.lt_def] at hij

def certificate : CheckedCertificate where
  certificate := { sizePred := 6, points := points, selected := extend selected }
  checked := extend_checked points selected reduced_checked

end C000673

end HexagonCover.NBand.Support.Run0013
