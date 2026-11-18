import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0011
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B0931 : Block := .branch 160 ![385, 374144419156711147060143317175368453172656219358722, 9295429630892709892, 24584, 98320, 393248, 16747358238031692654545439388446389205205056] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 595).pointIds 595), (.leaf 2 (Common.fact 596).pointIds 596), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 597).pointIds 597)]
theorem treeEq0931 : B0931.tree = HexagonCover.N7900.SplitData.node0931 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0930 : Block := .branch 168 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 16747358238031692654545439388446389205205056] ![(.leaf 0 (Common.fact 590).pointIds 590), B0931, (.leaf 2 (Common.fact 591).pointIds 591), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0930 : B0930.tree = HexagonCover.N7900.SplitData.node0930 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0931
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0929 : Block := .branch 142 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 11876128051006292170285997551789249029840834756624, 5708990770823839524233143877797980545531379744, 11172171938399036869161509820284298828709952] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 496).pointIds 496), B0930]
theorem treeEq0929 : B0929.tree = HexagonCover.N7900.SplitData.node0929 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0930

def B0928 : Block := .branch 163 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 11172171938399036869161509820284298828709952] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B0929, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 588).pointIds 588)]
theorem treeEq0928 : B0928.tree = HexagonCover.N7900.SplitData.node0928 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0929
  · rfl
  · rfl

def B0927 : Block := .branch 143 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114955081327760024026597765981732047520104464, 5708990770823839524233143877797980545531379744, 21799339133725298393650683960118075719744] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 122).pointIds 122), B0928]
theorem treeEq0927 : B0927.tree = HexagonCover.N7900.SplitData.node0927 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0928

def B0926 : Block := .branch 131 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21799339133725298393650683960118075719744] ![(.leaf 0 (Common.fact 581).pointIds 581), (.leaf 1 (Common.fact 582).pointIds 582), (.leaf 2 (Common.fact 583).pointIds 583), (.leaf 3 (Common.fact 584).pointIds 584), B0927, (.leaf 5 (Common.fact 585).pointIds 585), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0926 : B0926.tree = HexagonCover.N7900.SplitData.node0926 := by
  change Tree.branch (131 : Fin 170) _ = Tree.branch (131 : Fin 170) _
  apply congrArg (Tree.branch (131 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0927
  · rfl
  · rfl

def B0925 : Block := .branch 135 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21799339133725298393650683960118075719744] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 576).pointIds 576), (.leaf 2 (Common.fact 577).pointIds 577), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 579).pointIds 579), B0926, (.leaf 6 (Common.fact 580).pointIds 580)]
theorem treeEq0925 : B0925.tree = HexagonCover.N7900.SplitData.node0925 := by
  change Tree.branch (135 : Fin 170) _ = Tree.branch (135 : Fin 170) _
  apply congrArg (Tree.branch (135 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0926
  · rfl

def B0924 : Block := .branch 101 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21799339131189997193194225157124669308992] ![(.leaf 0 (Common.fact 569).pointIds 569), (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), B0925]
theorem treeEq0924 : B0924.tree = HexagonCover.N7900.SplitData.node0924 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0925

def B0923 : Block := .branch 124 ![42535295867593188601788396837474926977, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 568).pointIds 568), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0924]
theorem treeEq0923 : B0923.tree = HexagonCover.N7900.SplitData.node0923 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0924

def B0922 : Block := .branch 125 ![2475880668866570908503900545, 140737488356866, 9295429630892709892, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 748294547304193117959810867494614704044382993383456, 21778071483257438539227764244160183795776] ![B0923, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0922 : B0922.tree = HexagonCover.N7900.SplitData.node0922 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0923
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0921 : Block := .branch 157 ![2475880668866570908503900545, 140737488356866, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B0922, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq0921 : B0921.tree = HexagonCover.N7900.SplitData.node0921 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0922
  · rfl
  · rfl

def B0920 : Block := .branch 166 ![2475880668866570908503900545, 140737488356866, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 21778071483257438539227764244160183795776] ![B0921, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0920 : B0920.tree = HexagonCover.N7900.SplitData.node0920 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0921
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0919 : Block := .branch 169 ![10143680682494701782882129543553, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1430035285855776208950977934233576181571092496, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 565).pointIds 565), B0920, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0919 : B0919.tree = HexagonCover.N7900.SplitData.node0919 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0920
  · rfl

def B0918 : Block := .branch 141 ![10143680682494701782882129543553, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), B0919, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 564).pointIds 564)]
theorem treeEq0918 : B0918.tree = HexagonCover.N7900.SplitData.node0918 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0919
  · rfl
  · rfl

def B0917 : Block := .branch 144 ![10143680682494701782882129543553, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0918, (.leaf 6 (Common.fact 563).pointIds 563)]
theorem treeEq0917 : B0917.tree = HexagonCover.N7900.SplitData.node0917 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0918
  · rfl

theorem accepted0917 : B0917.accepted = true := by decide +kernel
theorem checked0917 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0917 (maskNeeds ![10143680682494701782882129543553, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152]) := by
  rw [← treeEq0917]
  exact B0917.sound accepted0917
#print axioms checked0917

def B0941 : Block := .branch 124 ![10384593717674118166868307245793665, 1538, 6148, 24584, 98320, 393248, 11692024270797894094198023816860296433899633377344] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq0941 : B0941.tree = HexagonCover.N7900.SplitData.node0941 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0940 : Block := .branch 143 ![10384593717674118166868307245793665, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886453049001160109718880387136] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 517).pointIds 517), (.leaf 5 (Common.fact 122).pointIds 122), B0941]
theorem treeEq0940 : B0940.tree = HexagonCover.N7900.SplitData.node0940 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0941

def B0939 : Block := .branch 101 ![10384593717674118166868307245793665, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886453049001160109718880387136] ![B0940, (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0939 : B0939.tree = HexagonCover.N7900.SplitData.node0939 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0940
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0938 : Block := .branch 163 ![10384593717674118166868307245793665, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 247).pointIds 247), B0939]
theorem treeEq0938 : B0938.tree = HexagonCover.N7900.SplitData.node0938 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0939

def B0937 : Block := .branch 169 ![10394734922475944002080280871436673, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071483257129129775806625005782433856] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), B0938, (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0937 : B0937.tree = HexagonCover.N7900.SplitData.node0937 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0938
  · rfl
  · rfl

def B0936 : Block := .branch 125 ![10394734922475944002080280871436673, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), B0937, (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0936 : B0936.tree = HexagonCover.N7900.SplitData.node0936 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0937
  · rfl

def B0943 : Block := .branch 133 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483256974991733805759786007396416] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 164).pointIds 164), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0943 : B0943.tree = HexagonCover.N7900.SplitData.node0943 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0942 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483256974991733805759786007396416] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B0943, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0942 : B0942.tree = HexagonCover.N7900.SplitData.node0942 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0943
  · rfl
  · rfl

def B0935 : Block := .branch 79 ![10394734921871481092272966284083585, 618970019786946063013774850, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![B0936, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0942]
theorem treeEq0935 : B0935.tree = HexagonCover.N7900.SplitData.node0935 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0936
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0942

def B0951 : Block := .branch 101 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 21799339131190152011256999555573355118656] ![(.leaf 0 (Common.fact 611).pointIds 611), (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0951 : B0951.tree = HexagonCover.N7900.SplitData.node0951 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0950 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 21778071483257593357290538642608869605440] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0951]
theorem treeEq0950 : B0950.tree = HexagonCover.N7900.SplitData.node0950 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0951

def B0949 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483258057584805270660211956777024] ![B0950, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0949 : B0949.tree = HexagonCover.N7900.SplitData.node0949 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0950
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0948 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B0949, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq0948 : B0948.tree = HexagonCover.N7900.SplitData.node0948 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0949
  · rfl
  · rfl

def B0947 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483258057584805270660211956777024] ![B0948, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0947 : B0947.tree = HexagonCover.N7900.SplitData.node0947 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0948
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0946 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B0947, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0946 : B0946.tree = HexagonCover.N7900.SplitData.node0946 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0947
  · rfl

def B0945 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0946, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0945 : B0945.tree = HexagonCover.N7900.SplitData.node0945 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0946
  · rfl
  · rfl

def B0944 : Block := .branch 144 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0945, (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq0944 : B0944.tree = HexagonCover.N7900.SplitData.node0944 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0945
  · rfl

def B0934 : Block := .branch 89 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 600).pointIds 600), B0935, (.leaf 2 (Common.fact 521).pointIds 521), (.leaf 3 (Common.fact 522).pointIds 522), (.leaf 4 (Common.fact 523).pointIds 523), (.leaf 5 (Common.fact 524).pointIds 524), B0944]
theorem treeEq0934 : B0934.tree = HexagonCover.N7900.SplitData.node0934 := by
  change Tree.branch (89 : Fin 170) _ = Tree.branch (89 : Fin 170) _
  apply congrArg (Tree.branch (89 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0935
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0944

theorem accepted0934 : B0934.accepted = true := by decide +kernel
theorem checked0934 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0934 (maskNeeds ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq0934]
  exact B0934.sound accepted0934
#print axioms checked0934

def Tip0908_0917 : Block := .tip HexagonCover.N7900.SplitData.node0917 ![10143680682494701782882129543553, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152] checked0917
def Tip0908_0934 : Block := .tip HexagonCover.N7900.SplitData.node0934 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] checked0934
def B0916 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 11692024270797894094198487968817164725588397129792] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 562).pointIds 562)]
theorem treeEq0916 : B0916.tree = HexagonCover.N7900.SplitData.node0916 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0915 : Block := .branch 143 ![1267650600228229401496703205761, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886917200958028401407644139584] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 517).pointIds 517), (.leaf 5 (Common.fact 122).pointIds 122), B0916]
theorem treeEq0915 : B0915.tree = HexagonCover.N7900.SplitData.node0915 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0916

def B0914 : Block := .branch 113 ![1267650600228229401496703205761, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886917200958028401407644139584] ![B0915, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 560).pointIds 560)]
theorem treeEq0914 : B0914.tree = HexagonCover.N7900.SplitData.node0914 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0915
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0913 : Block := .branch 163 ![1267650600228229401496703205761, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 247).pointIds 247), B0914]
theorem treeEq0913 : B0913.tree = HexagonCover.N7900.SplitData.node0913 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0914

def B0912 : Block := .branch 169 ![11408855402054064613470328848769, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), B0913, (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0912 : B0912.tree = HexagonCover.N7900.SplitData.node0912 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0913
  · rfl
  · rfl

def B0911 : Block := .branch 125 ![11408855402054064613470328848769, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 557).pointIds 557), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), B0912, (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0911 : B0911.tree = HexagonCover.N7900.SplitData.node0911 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0912
  · rfl

def B0910 : Block := .branch 100 ![10143680682494701782882129543553, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0911, (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), Tip0908_0917]
theorem treeEq0910 : B0910.tree = HexagonCover.N7900.SplitData.node0910 := by
  change Tree.branch (100 : Fin 170) _ = Tree.branch (100 : Fin 170) _
  apply congrArg (Tree.branch (100 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0911
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0954 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0954 : B0954.tree = HexagonCover.N7900.SplitData.node0954 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0953 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0954, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 614).pointIds 614)]
theorem treeEq0953 : B0953.tree = HexagonCover.N7900.SplitData.node0953 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0954
  · rfl
  · rfl

def B0952 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0953, (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0952 : B0952.tree = HexagonCover.N7900.SplitData.node0952 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0953
  · rfl

def B0933 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 599).pointIds 599), Tip0908_0934, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0952]
theorem treeEq0933 : B0933.tree = HexagonCover.N7900.SplitData.node0933 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0952

def B0932 : Block := .branch 113 ![10141204802416131022332331295105, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![B0933, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 598).pointIds 598)]
theorem treeEq0932 : B0932.tree = HexagonCover.N7900.SplitData.node0932 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0933
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0909 : Block := .branch 76 ![10143680682494701782882129543553, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B0910, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0932]
theorem treeEq0909 : B0909.tree = HexagonCover.N7900.SplitData.node0909 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0910
  · rfl
  · rfl
  · rfl
  · exact treeEq0932

def B0957 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054513090804270811840576] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 618).pointIds 618)]
theorem treeEq0957 : B0957.tree = HexagonCover.N7900.SplitData.node0957 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0956 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054513090804270811840576] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0957, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 617).pointIds 617)]
theorem treeEq0956 : B0956.tree = HexagonCover.N7900.SplitData.node0956 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0957
  · rfl
  · rfl

def B0955 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054513090804270811840576] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0956, (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0955 : B0955.tree = HexagonCover.N7900.SplitData.node0955 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0956
  · rfl

def B0908 : Block := .branch 68 ![10143680682494701782882129543553, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 550).pointIds 550), B0909, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B0955]
theorem treeEq0908 : B0908.tree = HexagonCover.N7900.SplitData.node0908 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0909
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0955

theorem accepted0908 : B0908.accepted = true := by decide +kernel
theorem checked0908 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0908 (maskNeeds ![10143680682494701782882129543553, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0908]
  exact B0908.sound accepted0908
#print axioms checked0908

def B0903 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0903 : B0903.tree = HexagonCover.N7900.SplitData.node0903 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0902 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0903]
theorem treeEq0902 : B0902.tree = HexagonCover.N7900.SplitData.node0902 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0903

def B0901 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0902, (.leaf 0 [] 0)]
theorem treeEq0901 : B0901.tree = HexagonCover.N7900.SplitData.node0901 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0902
  · rfl

def B0900 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0901, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0900 : B0900.tree = HexagonCover.N7900.SplitData.node0900 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0901
  · rfl

def B0899 : Block := .branch 169 ![10141204801825835211973625643393, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), B0900, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0899 : B0899.tree = HexagonCover.N7900.SplitData.node0899 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0900
  · rfl
  · rfl

def B0898 : Block := .branch 114 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0899, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0898 : B0898.tree = HexagonCover.N7900.SplitData.node0898 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0899
  · rfl

def B0897 : Block := .branch 132 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0898]
theorem treeEq0897 : B0897.tree = HexagonCover.N7900.SplitData.node0897 := by
  change Tree.branch (132 : Fin 170) _ = Tree.branch (132 : Fin 170) _
  apply congrArg (Tree.branch (132 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0898

def B0896 : Block := .branch 68 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 546).pointIds 546), B0897, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0896 : B0896.tree = HexagonCover.N7900.SplitData.node0896 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0897
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0895 : Block := .branch 133 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0896]
theorem treeEq0895 : B0895.tree = HexagonCover.N7900.SplitData.node0895 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0896

def B0894 : Block := .branch 138 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0895, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0894 : B0894.tree = HexagonCover.N7900.SplitData.node0894 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0895
  · rfl
  · rfl

def B0893 : Block := .branch 144 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0894, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0893 : B0893.tree = HexagonCover.N7900.SplitData.node0893 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0894
  · rfl

def B0892 : Block := .branch 124 ![10141205104057290115630919319937, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 545).pointIds 545), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0893]
theorem treeEq0892 : B0892.tree = HexagonCover.N7900.SplitData.node0892 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0893

def B0906 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0906 : B0906.tree = HexagonCover.N7900.SplitData.node0906 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0905 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0906, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 548).pointIds 548)]
theorem treeEq0905 : B0905.tree = HexagonCover.N7900.SplitData.node0905 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0906
  · rfl
  · rfl

def B0904 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0905, (.leaf 6 (Common.fact 547).pointIds 547)]
theorem treeEq0904 : B0904.tree = HexagonCover.N7900.SplitData.node0904 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0905
  · rfl

def B0891 : Block := .branch 78 ![10141204801825835211973625643393, 309485010542061746592417282, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0892, (.leaf 1 (Common.fact 544).pointIds 544), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0904]
theorem treeEq0891 : B0891.tree = HexagonCover.N7900.SplitData.node0891 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0892
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0904

theorem accepted0891 : B0891.accepted = true := by decide +kernel
theorem checked0891 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0891 (maskNeeds ![10141204801825835211973625643393, 309485010542061746592417282, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0891]
  exact B0891.sound accepted0891
#print axioms checked0891

end HexagonCover.N7900.SplitAlignedTree.Run0011
