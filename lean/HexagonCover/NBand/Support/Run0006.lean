import HexagonCover.SupportInteger

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.Support.Run0006
open DistanceLeaf SupportWitness SupportWitnessSymmetry

namespace C000287
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(6000,0),(0,-6000)⟩,⟨(6000,0),(0,0)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000287

namespace C000288
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(6000,0),(0,-6000)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(5000,0),(0,-1000)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000288

namespace C000289
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(6000,0),(0,-6000)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(8000,0),(0,0)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000289

namespace C000290
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-1,0),(0,-1)⟩,⟨(-2,0),(0,0)⟩,⟨(1,0),(0,5)⟩,⟨(8,0),(0,0)⟩,⟨(5,0),(0,-1)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

end C000290

namespace C000291
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-1,0),(0,-1)⟩,⟨(-2,0),(0,0)⟩,⟨(1,0),(0,5)⟩,⟨(5,0),(0,-1)⟩,⟨(7,0),(0,1)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

end C000291

namespace C000292
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(6000,0),(0,-6000)⟩,⟨(2000,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(8000,0),(0,-2000)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000292

namespace C000293
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(1000,0),(0,-5000)⟩,⟨(6000,0),(0,-6000)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(8000,0),(0,-2000)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000293

namespace C000294
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(0,0),(0,-4000)⟩,⟨(6000,0),(0,-6000)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000294

namespace C000295
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-1000,0),(0,-3000)⟩,⟨(6000,0),(0,-6000)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000295

namespace C000296
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-50,0),(0,-150)⟩,⟨(-300,0),(0,-300)⟩,⟨(-399,0),(0,-201)⟩,⟨(100,0),(0,-300)⟩,⟨(100,0),(0,-200)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 600 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 600 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

end C000296

namespace C000297
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-2000,0),(0,-2000)⟩,⟨(6000,0),(0,-6000)⟩,⟨(2040,0),(0,-6000)⟩,⟨(1990,0),(0,-1990)⟩,⟨(9101,0),(0,-2899)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 12000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 12000 (by decide) integerPoints
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

end C000297

namespace C000298
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-325000,0),(0,-325000)⟩,⟨(-650000,0),(0,0)⟩,⟨(325000,0),(0,1625000)⟩,⟨(975000,0),(0,1625000)⟩,⟨(650000,0),(0,0)⟩,⟨(165825,0),(-397980,0)⟩,⟨(258687,0),(-344916,0)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 3900000 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_5_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

end C000298

namespace C000299
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-4325,0),(0,-4325)⟩,⟨(-8650,0),(0,0)⟩,⟨(4325,0),(0,21625)⟩,⟨(33216,0),(0,-1500)⟩,⟨(30275,0),(0,-4325)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

end C000299

namespace C000300
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-65000,0),(0,-65000)⟩,⟨(-65000,0),(0,195000)⟩,⟨(-130000,0),(0,0)⟩,⟨(33165,0),(-79596,0)⟩,⟨(585000,0),(0,65000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 780000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 780000 (by decide) integerPoints
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

end C000300

namespace C000301
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-60000,0),(0,0)⟩,⟨(-30000,0),(0,0)⟩,⟨(-20000,0),(0,-20000)⟩,⟨(-40149,0),(0,-19851)⟩,⟨(-50100,0),(0,9900)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 60000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 60000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

end C000301

namespace C000302
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-325000,0),(0,-325000)⟩,⟨(-325000,0),(0,975000)⟩,⟨(-650000,0),(0,0)⟩,⟨(975000,0),(0,1625000)⟩,⟨(650000,0),(0,0)⟩,⟨(165825,0),(-397980,0)⟩,⟨(258687,0),(-344916,0)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 3900000 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_5_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

end C000302

namespace C000303
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-51900,0),(0,51900)⟩,⟨(-17646,0),(0,51900)⟩,⟨(-86500,0),(0,17300)⟩,⟨(-26469,0),(0,300)⟩]
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

def e_0_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 3 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 3 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
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

def e_2_3_1_selection : Selection 3 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

end C000303

namespace C000304
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-56225000,0),(0,-56225000)⟩,⟨(-56225000,0),(0,168675000)⟩,⟨(-172048500,0),(0,1950000)⟩,⟨(449800000,0),(0,112450000)⟩,⟨(28687725,0),(-68850540,0)⟩,⟨(44752851,0),(-59670468,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 674700000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

end C000304

namespace C000305
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(1038000,0),(0,-1038000)⟩,⟨(1038000,0),(0,0)⟩,⟨(352920,0),(0,-1038000)⟩,⟨(238740,0),(0,-756000)⟩,⟨(1574473,0),(0,-501527)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 2076000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 2076000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

end C000305

namespace C000306
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-8650,0),(0,25950)⟩,⟨(-26469,0),(0,300)⟩,⟨(51900,0),(0,0)⟩,⟨(51381,0),(0,-12600)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

end C000306

namespace C000307
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-56225000,0),(0,-56225000)⟩,⟨(-56225000,0),(0,168675000)⟩,⟨(-172048500,0),(0,1950000)⟩,⟨(56225000,0),(0,281125000)⟩,⟨(374458500,0),(0,93600000)⟩,⟨(28687725,0),(-68850540,0)⟩,⟨(44752851,0),(-59670468,0)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 674700000 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

end C000307

namespace C000308
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-8650,0),(0,25950)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,43250)⟩,⟨(66432,0),(0,-3000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

end C000308

namespace C000309
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-325000,0),(0,-325000)⟩,⟨(-975000,0),(0,325000)⟩,⟨(975000,0),(0,1625000)⟩,⟨(650000,0),(0,0)⟩,⟨(165825,0),(-397980,0)⟩,⟨(258687,0),(-344916,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 3900000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 5 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def pair_1_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 3900000 (by decide) integerPoints
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

end C000309

namespace C000310
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-150000,0),(0,-100000)⟩,⟨(-75000,0),(0,25000)⟩,⟨(25000,0),(0,25000)⟩,⟨(50000,0),(0,0)⟩,⟨(19899,0),(-26532,0)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 300000 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨1, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 300000 (by decide) integerPoints
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

end C000310

namespace C000311
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-103800,0),(0,0)⟩,⟨(-86673,0),(0,17127)⟩,⟨(-69200,0),(0,-34600)⟩,⟨(-43250,0),(0,8650)⟩,⟨(-26469,0),(0,300)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_0_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_0_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

end C000311

namespace C000312
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-56225000,0),(0,-56225000)⟩,⟨(-168675000,0),(0,56225000)⟩,⟨(-172048500,0),(0,1950000)⟩,⟨(449800000,0),(0,112450000)⟩,⟨(28687725,0),(-68850540,0)⟩,⟨(44752851,0),(-59670468,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 674700000 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

end C000312

namespace C000313
def integerPoints : Fin 4 → SupportInteger.Point := ![⟨(-25950,0),(0,25950)⟩,⟨(-6747,0),(0,6750)⟩,⟨(-8823,0),(0,25950)⟩,⟨(-43250,0),(0,8650)⟩]
def points : Fin 4 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 3 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 3 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 3 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_1_selection : Selection 3 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

end C000313

namespace C000314
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(34600,0),(0,-34600)⟩,⟨(17300,0),(0,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
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

end C000314

namespace C000315
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(25950,0),(0,-43250)⟩,⟨(17300,0),(0,0)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_0_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 4 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 4 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_2_4_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_1_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

end C000315

namespace C000316
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(51900,0),(0,0)⟩,⟨(51381,0),(0,-12600)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_1_selection : Selection 5 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_3_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
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

end C000316

namespace C000317
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(0,0),(0,-17300)⟩,⟨(51900,0),(0,0)⟩,⟨(51381,0),(0,-12600)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
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

end C000317

namespace C000318
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,-25950)⟩,⟨(8650,0),(0,8650)⟩,⟨(51900,0),(0,-17300)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

end C000318

namespace C000319
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,-25950)⟩,⟨(51900,0),(0,0)⟩,⟨(51381,0),(0,-12600)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
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

end C000319

namespace C000320
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(51900,0),(0,0)⟩,⟨(11937,0),(0,-37800)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 4 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 4 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_0_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
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

def e_1_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 4 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 4 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

end C000320

namespace C000321
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-51900,0),(0,-17300)⟩,⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(8650,0),(0,-25950)⟩,⟨(8650,0),(0,8650)⟩,⟨(25950,0),(0,-8650)⟩,⟨(34427,0),(0,0)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_2_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_5_6_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

end C000321

namespace C000322
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-43250,0),(0,-8650)⟩,⟨(8650,0),(0,-25950)⟩,⟨(8650,0),(0,8650)⟩,⟨(25950,0),(0,-8650)⟩,⟨(34427,0),(0,0)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_5_6_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

end C000322

namespace C000323
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-56225000,0),(0,-56225000)⟩,⟨(-168675000,0),(0,56225000)⟩,⟨(-172048500,0),(0,1950000)⟩,⟨(112450000,0),(0,0)⟩,⟨(28687725,0),(-68850540,0)⟩,⟨(44752851,0),(-59670468,0)⟩,⟨(393575000,0),(0,168675000)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 674700000 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_0_6_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_0_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    true e_0_6_1_selection (by decide +kernel)

def pair_0_6 : Bool → Selection 6 :=
  fun b => if b then e_0_6_1_selection else e_0_6_0_selection

def pair_1_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def pair_1_1 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_1_2_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_1_6_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_1_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_2_3_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_6_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_2_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_3_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_3_6_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_3_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_4_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_4_6_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_4_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

def e_5_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨3, by decide⟩,⟨6, by decide⟩,⟨2, by decide⟩]
theorem e_5_6_1 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ true e_5_6_1_selection = true := by
  exact SupportInteger.eventCheck_sound 674700000 (by decide) integerPoints
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

end C000323

namespace C000324
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,-43250)⟩,⟨(8650,0),(0,8650)⟩,⟨(17300,0),(0,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨3, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

end C000324

namespace C000325
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(17300,0),(0,-34600)⟩,⟨(34427,0),(0,0)⟩,⟨(11937,0),(0,-37800)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_0_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
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

def e_4_5_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
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

def e_5_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨5, by decide⟩]
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

end C000325

namespace C000326
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(17300,0),(0,-34600)⟩,⟨(34427,0),(0,0)⟩,⟨(43250,0),(0,-8650)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_1_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨3, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_3_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_4_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_5_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

end C000326

namespace C000327
def integerPoints : Fin 5 → SupportInteger.Point := ![⟨(-8650,0),(0,-8650)⟩,⟨(-25950,0),(0,8650)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(66432,0),(0,-3000)⟩]
def points : Fin 5 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 4 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 4 := ![⟨2, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_0_2_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_0_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_0_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 4 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 4 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨4, by decide⟩]
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

def e_1_3_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 4 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

def e_2_3_0_selection : Selection 4 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 4 := ![⟨4, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_2_4_1_selection : Selection 4 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 4 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨4, by decide⟩]
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

end C000327

namespace C000328
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,-25950)⟩,⟨(43250,0),(0,8650)⟩,⟨(51381,0),(0,-12600)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
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

end C000328

namespace C000329
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(17300,0),(0,-34600)⟩,⟨(11937,0),(0,-37800)⟩,⟨(43250,0),(0,8650)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨4, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨4, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨4, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨4, by decide⟩]
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

end C000329

namespace C000330
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,-8650)⟩,⟨(-12975,0),(0,4325)⟩,⟨(-6747,0),(0,6750)⟩,⟨(4325,0),(0,-12975)⟩,⟨(4325,0),(0,4325)⟩,⟨(17300,0),(0,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_0_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
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

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨2, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨0, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
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

end C000330

namespace C000331
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-12975,0),(0,4325)⟩,⟨(-6747,0),(0,6750)⟩,⟨(-21625,0),(0,-4325)⟩,⟨(4325,0),(0,-12975)⟩,⟨(4325,0),(0,4325)⟩,⟨(17300,0),(0,0)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 51900 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
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

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨3, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨3, by decide⟩,⟨1, by decide⟩]
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

def e_1_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨2, by decide⟩]
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

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨3, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 51900 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

end C000331

namespace C000332
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(34600,0),(0,0)⟩,⟨(17300,0),(0,-34600)⟩,⟨(11937,0),(0,-37800)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_0_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_1_5_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_1_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_1_5_1_selection (by decide +kernel)

def pair_1_5 : Bool → Selection 6 :=
  fun b => if b then e_1_5_1_selection else e_1_5_0_selection

def e_1_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_1_6_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_1_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_1_6_0_selection (by decide +kernel)

def e_1_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨6, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨6, by decide⟩,⟨4, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨6, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
theorem e_3_5_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_3_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_3_5_1_selection (by decide +kernel)

def pair_3_5 : Bool → Selection 6 :=
  fun b => if b then e_3_5_1_selection else e_3_5_0_selection

def e_3_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_3_6_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_3_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_3_6_0_selection (by decide +kernel)

def e_3_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨3, by decide⟩]
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

def e_4_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
theorem e_4_5_1 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_4_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_4_5_1_selection (by decide +kernel)

def pair_4_5 : Bool → Selection 6 :=
  fun b => if b then e_4_5_1_selection else e_4_5_0_selection

def e_4_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨6, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
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

def e_5_6_0_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨6, by decide⟩,⟨4, by decide⟩]
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

end C000332

namespace C000333
def integerPoints : Fin 7 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(8650,0),(0,8650)⟩,⟨(34600,0),(0,0)⟩,⟨(17300,0),(0,-34600)⟩,⟨(43250,0),(0,-8650)⟩]
def points : Fin 7 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 6 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨3, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 6 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 6 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 6 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 6 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_5_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_0_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_0_5_1_selection (by decide +kernel)

def pair_0_5 : Bool → Selection 6 :=
  fun b => if b then e_0_5_1_selection else e_0_5_0_selection

def e_0_6_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_6_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_0_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_0_6_0_selection (by decide +kernel)

def e_0_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
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

def e_1_2_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 6 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 6 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 6 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_1_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨5, by decide⟩,⟨6, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 6 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 6 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_2_5_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ true e_2_5_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    true e_2_5_1_selection (by decide +kernel)

def pair_2_5 : Bool → Selection 6 :=
  fun b => if b then e_2_5_1_selection else e_2_5_0_selection

def e_2_6_0_selection : Selection 6 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_2_6_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_2_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_2_6_0_selection (by decide +kernel)

def e_2_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨0, by decide⟩]
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

def e_3_4_0_selection : Selection 6 := ![⟨3, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 6 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨3, by decide⟩]
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

def e_3_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨6, by decide⟩,⟨1, by decide⟩]
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

def e_4_5_0_selection : Selection 6 := ![⟨6, by decide⟩,⟨1, by decide⟩,⟨5, by decide⟩]
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

def e_4_6_0_selection : Selection 6 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_6_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_4_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_4_6_0_selection (by decide +kernel)

def e_4_6_1_selection : Selection 6 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_5_6_0_selection : Selection 6 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_5_6_0 : eventCheck points (points ⟨5, by decide⟩) (points ⟨6, by decide⟩)
    ⟨0, by decide⟩ false e_5_6_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨5, by decide⟩) (integerPoints ⟨6, by decide⟩)
    false e_5_6_0_selection (by decide +kernel)

def e_5_6_1_selection : Selection 6 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
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

end C000333

namespace C000334
def integerPoints : Fin 6 → SupportInteger.Point := ![⟨(-25950,0),(0,8650)⟩,⟨(-13494,0),(0,13500)⟩,⟨(-26469,0),(0,300)⟩,⟨(0,0),(0,-17300)⟩,⟨(25950,0),(0,8650)⟩,⟨(43250,0),(0,-25950)⟩]
def points : Fin 6 → ExactPoint := fun i => SupportInteger.decode 103800 (integerPoints i)

def pair_0_0 : Bool → Selection 5 :=
  fun _ => ![⟨0, by decide⟩,⟨0, by decide⟩,⟨0, by decide⟩]

def e_0_1_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_0_1_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ false e_0_1_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    false e_0_1_0_selection (by decide +kernel)

def e_0_1_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨2, by decide⟩]
theorem e_0_1_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨1, by decide⟩)
    ⟨0, by decide⟩ true e_0_1_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨1, by decide⟩)
    true e_0_1_1_selection (by decide +kernel)

def pair_0_1 : Bool → Selection 5 :=
  fun b => if b then e_0_1_1_selection else e_0_1_0_selection

def e_0_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨3, by decide⟩]
theorem e_0_2_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_0_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_0_2_0_selection (by decide +kernel)

def e_0_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_0_2_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_0_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_0_2_1_selection (by decide +kernel)

def pair_0_2 : Bool → Selection 5 :=
  fun b => if b then e_0_2_1_selection else e_0_2_0_selection

def e_0_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_3_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_0_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_0_3_0_selection (by decide +kernel)

def e_0_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_0_3_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_0_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_0_3_1_selection (by decide +kernel)

def pair_0_3 : Bool → Selection 5 :=
  fun b => if b then e_0_3_1_selection else e_0_3_0_selection

def e_0_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_0_4_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_0_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_0_4_0_selection (by decide +kernel)

def e_0_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_0_4_1 : eventCheck points (points ⟨0, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_0_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_0_4_1_selection (by decide +kernel)

def pair_0_4 : Bool → Selection 5 :=
  fun b => if b then e_0_4_1_selection else e_0_4_0_selection

def e_0_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_0_5_0 : eventCheck points (points ⟨0, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_0_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨0, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_0_5_0_selection (by decide +kernel)

def e_0_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_1_2_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_1_2_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ false e_1_2_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    false e_1_2_0_selection (by decide +kernel)

def e_1_2_1_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_2_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨2, by decide⟩)
    ⟨0, by decide⟩ true e_1_2_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨2, by decide⟩)
    true e_1_2_1_selection (by decide +kernel)

def pair_1_2 : Bool → Selection 5 :=
  fun b => if b then e_1_2_1_selection else e_1_2_0_selection

def e_1_3_0_selection : Selection 5 := ![⟨5, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_3_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_1_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_1_3_0_selection (by decide +kernel)

def e_1_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_1_3_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_1_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_1_3_1_selection (by decide +kernel)

def pair_1_3 : Bool → Selection 5 :=
  fun b => if b then e_1_3_1_selection else e_1_3_0_selection

def e_1_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_1_4_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_1_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_1_4_0_selection (by decide +kernel)

def e_1_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_1_4_1 : eventCheck points (points ⟨1, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_1_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_1_4_1_selection (by decide +kernel)

def pair_1_4 : Bool → Selection 5 :=
  fun b => if b then e_1_4_1_selection else e_1_4_0_selection

def e_1_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_1_5_0 : eventCheck points (points ⟨1, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_1_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨1, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_1_5_0_selection (by decide +kernel)

def e_1_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_2_3_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_3_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ false e_2_3_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    false e_2_3_0_selection (by decide +kernel)

def e_2_3_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
theorem e_2_3_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨3, by decide⟩)
    ⟨0, by decide⟩ true e_2_3_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨3, by decide⟩)
    true e_2_3_1_selection (by decide +kernel)

def pair_2_3 : Bool → Selection 5 :=
  fun b => if b then e_2_3_1_selection else e_2_3_0_selection

def e_2_4_0_selection : Selection 5 := ![⟨1, by decide⟩,⟨3, by decide⟩,⟨5, by decide⟩]
theorem e_2_4_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_2_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_2_4_0_selection (by decide +kernel)

def e_2_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩]
theorem e_2_4_1 : eventCheck points (points ⟨2, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_2_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_2_4_1_selection (by decide +kernel)

def pair_2_4 : Bool → Selection 5 :=
  fun b => if b then e_2_4_1_selection else e_2_4_0_selection

def e_2_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_2_5_0 : eventCheck points (points ⟨2, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_2_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨2, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_2_5_0_selection (by decide +kernel)

def e_2_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨1, by decide⟩]
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

def e_3_4_0_selection : Selection 5 := ![⟨0, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
theorem e_3_4_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ false e_3_4_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    false e_3_4_0_selection (by decide +kernel)

def e_3_4_1_selection : Selection 5 := ![⟨5, by decide⟩,⟨1, by decide⟩,⟨2, by decide⟩]
theorem e_3_4_1 : eventCheck points (points ⟨3, by decide⟩) (points ⟨4, by decide⟩)
    ⟨0, by decide⟩ true e_3_4_1_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨4, by decide⟩)
    true e_3_4_1_selection (by decide +kernel)

def pair_3_4 : Bool → Selection 5 :=
  fun b => if b then e_3_4_1_selection else e_3_4_0_selection

def e_3_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨2, by decide⟩,⟨5, by decide⟩]
theorem e_3_5_0 : eventCheck points (points ⟨3, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_3_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨3, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_3_5_0_selection (by decide +kernel)

def e_3_5_1_selection : Selection 5 := ![⟨3, by decide⟩,⟨5, by decide⟩,⟨0, by decide⟩]
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

def e_4_5_0_selection : Selection 5 := ![⟨4, by decide⟩,⟨0, by decide⟩,⟨5, by decide⟩]
theorem e_4_5_0 : eventCheck points (points ⟨4, by decide⟩) (points ⟨5, by decide⟩)
    ⟨0, by decide⟩ false e_4_5_0_selection = true := by
  exact SupportInteger.eventCheck_sound 103800 (by decide) integerPoints
    (integerPoints ⟨4, by decide⟩) (integerPoints ⟨5, by decide⟩)
    false e_4_5_0_selection (by decide +kernel)

def e_4_5_1_selection : Selection 5 := ![⟨2, by decide⟩,⟨5, by decide⟩,⟨4, by decide⟩]
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

end C000334

end HexagonCover.NBand.Support.Run0006
