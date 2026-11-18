import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0005
import HexagonCover.NBand.M7700_7900.SplitTree.Run0006
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0007
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0412_0423 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0423 ![385, 720716677867636226, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0006.checked0423
def B0417 : Block := .branch 91 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 1496577676648622659723830397755691755026766383022144] ![(.leaf 0 (Common.fact 675).pointIds 675), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), (.leaf 5 (Common.fact 345).pointIds 345), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0417 : B0417.tree = HexagonCover.NBand.M7700_7900.SplitData.node0417 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0416 : Block := .branch 170 ![288230376151712129, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 671).pointIds 671), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), B0417]
theorem treeEq0416 : B0416.tree = HexagonCover.NBand.M7700_7900.SplitData.node0416 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0417

def B0421 : Block := .branch 91 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 1496577676648622659723830397755691755026766383022144] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), (.leaf 5 (Common.fact 345).pointIds 345), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M7700_7900.SplitData.node0421 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0420 : Block := .branch 170 ![576460752303423873, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 678).pointIds 678), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), B0421]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M7700_7900.SplitData.node0420 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0421

def B0564 : Block := .branch 100 ![1496577676626844588240573268701473812127674924007809, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 540).pointIds 540), (.leaf 1 (Common.fact 489).pointIds 489), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 492).pointIds 492), (.leaf 5 (Common.fact 493).pointIds 493), (.leaf 6 (Common.fact 786).pointIds 786)]
theorem treeEq0564 : B0564.tree = HexagonCover.NBand.M7700_7900.SplitData.node0564 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0563 : Block := .branch 170 ![385, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![B0564, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq0563 : B0563.tree = HexagonCover.NBand.M7700_7900.SplitData.node0563 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0564
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0422 : Block := .branch 65 ![385, 1008947054019347970, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 679).pointIds 679), Tip0412_0423, (.leaf 3 (Common.fact 453).pointIds 453), (.leaf 4 (Common.fact 454).pointIds 454), (.leaf 5 (Common.fact 455).pointIds 455), B0563]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M7700_7900.SplitData.node0422 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0563

def B0419 : Block := .branch 59 ![385, 432486301715924482, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0420, B0422, (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq0419 : B0419.tree = HexagonCover.NBand.M7700_7900.SplitData.node0419 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0420
  · exact treeEq0422
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0418 : Block := .branch 64 ![385, 432486301715924482, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 677).pointIds 677), B0419, (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0418 : B0418.tree = HexagonCover.NBand.M7700_7900.SplitData.node0418 := by
  change Tree.branch (64 : Fin 172) _ = Tree.branch (64 : Fin 172) _
  apply congrArg (Tree.branch (64 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0419
  · rfl
  · rfl
  · rfl
  · rfl

def B0415 : Block := .branch 58 ![385, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0416, B0418, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 148).pointIds 148)]
theorem treeEq0415 : B0415.tree = HexagonCover.NBand.M7700_7900.SplitData.node0415 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0416
  · exact treeEq0418
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0414 : Block := .branch 150 ![385, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 98320, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), B0415, (.leaf 5 (Common.fact 110).pointIds 110), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0414 : B0414.tree = HexagonCover.NBand.M7700_7900.SplitData.node0414 := by
  change Tree.branch (150 : Fin 172) _ = Tree.branch (150 : Fin 172) _
  apply congrArg (Tree.branch (150 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0415
  · rfl
  · rfl

def B0413 : Block := .branch 152 ![385, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 86).pointIds 86), B0414, (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0413 : B0413.tree = HexagonCover.NBand.M7700_7900.SplitData.node0413 := by
  change Tree.branch (152 : Fin 172) _ = Tree.branch (152 : Fin 172) _
  apply congrArg (Tree.branch (152 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0414
  · rfl

def B0412 : Block := .branch 87 ![385, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 328).pointIds 328), (.leaf 1 (Common.fact 329).pointIds 329), (.leaf 2 (Common.fact 670).pointIds 670), (.leaf 3 (Common.fact 331).pointIds 331), (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), B0413]
theorem treeEq0412 : B0412.tree = HexagonCover.NBand.M7700_7900.SplitData.node0412 := by
  change Tree.branch (87 : Fin 172) _ = Tree.branch (87 : Fin 172) _
  apply congrArg (Tree.branch (87 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0413

theorem accepted0412 : B0412.accepted = true := by decide +kernel
theorem checked0412 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0412 (maskNeeds ![385, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0412]
  exact B0412.sound accepted0412
#print axioms checked0412

def Tip0021_0038 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0038 ![385, 504403158265497090, 9277485601127405572, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] HexagonCover.NBand.M7700_7900.SplitTree.Run0005.checked0038
def Tip0021_0412 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0412 ![385, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] checked0412
def B0037 : Block := .branch 79 ![288230376151712129, 216172782113785346, 6148, 24584, 98320, 393248, 27222599738585706796782283006458046447680] ![(.leaf 0 (Common.fact 208).pointIds 208), (.leaf 1 (Common.fact 209).pointIds 209), (.leaf 2 (Common.fact 210).pointIds 210), (.leaf 3 (Common.fact 211).pointIds 211), (.leaf 4 (Common.fact 212).pointIds 212), (.leaf 5 (Common.fact 213).pointIds 213), (.leaf 6 (Common.fact 214).pointIds 214)]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M7700_7900.SplitData.node0037 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0036 : Block := .branch 132 ![288230376151712129, 216172782113785346, 6148, 24584, 182689446912081499980393536567525428110234320912, 393248, 21778081867850691381368289287549755064384] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 206).pointIds 206), (.leaf 5 (Common.fact 207).pointIds 207), B0037]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M7700_7900.SplitData.node0036 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0037

def B0035 : Block := .branch 157 ![288230376151712129, 216172782113785346, 6148, 24584, 1742245718635204932932477990050653242753040, 43556142965880123323311949751266331459616, 21778081867850691381368289287549755064384] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0036, (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 0 [] 0)]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M7700_7900.SplitData.node0035 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0036
  · rfl
  · rfl

def B0034 : Block := .branch 135 ![288230376151712129, 216172782113785346, 6148, 24584, 1742245718635204932932477990050653242753040, 393248, 32667117609320722212196276725366337830976] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), B0035, (.leaf 6 (Common.fact 196).pointIds 196)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M7700_7900.SplitData.node0034 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0035
  · rfl

def B0033 : Block := .branch 140 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 32667117609320722212196276725366337830976] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0034, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 190).pointIds 190)]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M7700_7900.SplitData.node0033 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0034
  · rfl
  · rfl

def B0032 : Block := .branch 113 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 32667107224727005142541019664373679390784] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), (.leaf 5 (Common.fact 184).pointIds 184), B0033]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M7700_7900.SplitData.node0032 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0033

def B0031 : Block := .branch 64 ![288230376151712129, 147790125371790198274, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 32667107224727005142541019664373679390784] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B0032, (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M7700_7900.SplitData.node0031 := by
  change Tree.branch (64 : Fin 172) _ = Tree.branch (64 : Fin 172) _
  apply congrArg (Tree.branch (64 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0032
  · rfl
  · rfl
  · rfl
  · rfl

def B0030 : Block := .branch 67 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 32688374872659563796507480577338164904000] ![(.leaf 0 (Common.fact 167).pointIds 167), B0031, (.leaf 2 (Common.fact 168).pointIds 168), (.leaf 3 (Common.fact 169).pointIds 169), (.leaf 4 (Common.fact 170).pointIds 170), (.leaf 5 (Common.fact 171).pointIds 171), (.leaf 6 (Common.fact 172).pointIds 172)]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M7700_7900.SplitData.node0030 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0029 : Block := .branch 133 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 165).pointIds 165), (.leaf 5 (Common.fact 166).pointIds 166), B0030]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M7700_7900.SplitData.node0029 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0030

def B0028 : Block := .branch 138 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0029, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 160).pointIds 160)]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M7700_7900.SplitData.node0028 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0029
  · rfl
  · rfl

def B0027 : Block := .branch 124 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 149).pointIds 149), (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), B0028]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M7700_7900.SplitData.node0027 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0028

def B0026 : Block := .branch 58 ![385, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![B0027, Tip0021_0038, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 148).pointIds 148)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M7700_7900.SplitData.node0026 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0027
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0025 : Block := .branch 56 ![385, 144255925564212738, 9277485601127405572, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 139).pointIds 139), B0026, Tip0021_0412, (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 143).pointIds 143)]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M7700_7900.SplitData.node0025 := by
  change Tree.branch (56 : Fin 172) _ = Tree.branch (56 : Fin 172) _
  apply congrArg (Tree.branch (56 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0026
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0024 : Block := .branch 103 ![385, 144255925564212738, 9277485601127405572, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![B0025, (.leaf 1 (Common.fact 94).pointIds 94), (.leaf 2 (Common.fact 95).pointIds 95), (.leaf 3 (Common.fact 96).pointIds 96), (.leaf 4 (Common.fact 97).pointIds 97), (.leaf 5 (Common.fact 98).pointIds 98), (.leaf 6 (Common.fact 138).pointIds 138)]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M7700_7900.SplitData.node0024 := by
  change Tree.branch (103 : Fin 172) _ = Tree.branch (103 : Fin 172) _
  apply congrArg (Tree.branch (103 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0025
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0023 : Block := .branch 147 ![385, 144255925564212738, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), B0024, (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M7700_7900.SplitData.node0023 := by
  change Tree.branch (147 : Fin 172) _ = Tree.branch (147 : Fin 172) _
  apply congrArg (Tree.branch (147 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0024
  · rfl
  · rfl

def B0022 : Block := .branch 98 ![385, 144255925564212738, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 131).pointIds 131), (.leaf 1 (Common.fact 132).pointIds 132), (.leaf 2 (Common.fact 133).pointIds 133), (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), B0023]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M7700_7900.SplitData.node0022 := by
  change Tree.branch (98 : Fin 172) _ = Tree.branch (98 : Fin 172) _
  apply congrArg (Tree.branch (98 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0023

def B0021 : Block := .branch 85 ![385, 144255925564212738, 9277485601127405572, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 125).pointIds 125), (.leaf 1 (Common.fact 126).pointIds 126), (.leaf 2 (Common.fact 127).pointIds 127), B0022, (.leaf 4 (Common.fact 128).pointIds 128), (.leaf 5 (Common.fact 129).pointIds 129), (.leaf 6 (Common.fact 130).pointIds 130)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M7700_7900.SplitData.node0021 := by
  change Tree.branch (85 : Fin 172) _ = Tree.branch (85 : Fin 172) _
  apply congrArg (Tree.branch (85 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0022
  · rfl
  · rfl
  · rfl

theorem accepted0021 : B0021.accepted = true := by decide +kernel
theorem checked0021 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0021 (maskNeeds ![385, 144255925564212738, 9277485601127405572, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848]) := by
  rw [← treeEq0021]
  exact B0021.sound accepted0021
#print axioms checked0021

def B0604 : Block := .branch 79 ![1496577676626844588240573268702064107938033629659521, 216172782113785346, 6148, 24584, 98320, 393248, 2993155353280911765835138991357589382218418323193920] ![(.leaf 0 (Common.fact 814).pointIds 814), (.leaf 1 (Common.fact 209).pointIds 209), (.leaf 2 (Common.fact 210).pointIds 210), (.leaf 3 (Common.fact 211).pointIds 211), (.leaf 4 (Common.fact 212).pointIds 212), (.leaf 5 (Common.fact 213).pointIds 213), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M7700_7900.SplitData.node0604 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0603 : Block := .branch 132 ![1496577676626844588240573268702064107938033629659521, 216172782113785346, 6148, 24584, 182691537606943862226313055541113488894125506576, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 694).pointIds 694), (.leaf 5 (Common.fact 207).pointIds 207), B0604]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M7700_7900.SplitData.node0603 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0604

def B0602 : Block := .branch 157 ![1496577676626844588240573268702064107938033629659521, 216172782113785346, 6148, 24584, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0603, (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 0 [] 0)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M7700_7900.SplitData.node0602 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0603
  · rfl
  · rfl

def B0601 : Block := .branch 135 ![1496577676626844588240573268702064107938033629659521, 216172782113785346, 6148, 24584, 3832940580997450852451451578111437133938704, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), B0602, (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M7700_7900.SplitData.node0601 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0602
  · rfl

def B0600 : Block := .branch 76 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 24584, 3832940580997450852451451578111437133938704, 393248, 2993155353286356283705874006773003375937326614577216] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), B0601, (.leaf 3 (Common.fact 324).pointIds 324), (.leaf 4 (Common.fact 325).pointIds 325), (.leaf 5 (Common.fact 326).pointIds 326), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M7700_7900.SplitData.node0600 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0601
  · rfl
  · rfl
  · rfl
  · rfl

def B0599 : Block := .branch 133 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 24584, 1431080633286957331910737421027606573516685328, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 166).pointIds 166), B0600]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M7700_7900.SplitData.node0599 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0600

def B0598 : Block := .branch 138 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 79228162514264337593543974920, 1430732184143230290924150925429596442868154384, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0599, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M7700_7900.SplitData.node0598 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0599
  · rfl
  · rfl

def B0597 : Block := .branch 139 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 79228162514264337593543974920, 1430035285855776208950977934233576181571092496, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0598, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M7700_7900.SplitData.node0597 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0598
  · rfl
  · rfl

def B0596 : Block := .branch 140 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 79228162514264337593543974920, 1430035285855776208950977934233576181571092496, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0597, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 808).pointIds 808)]
theorem treeEq0596 : B0596.tree = HexagonCover.NBand.M7700_7900.SplitData.node0596 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0597
  · rfl
  · rfl

def B0595 : Block := .branch 141 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0596, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M7700_7900.SplitData.node0595 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0596
  · rfl
  · rfl

def B0594 : Block := .branch 144 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0595, (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M7700_7900.SplitData.node0594 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0595
  · rfl

def B0593 : Block := .branch 171 ![1496577676626844588240573268702064107938033629659521, 302231671076439407461890, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0594]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M7700_7900.SplitData.node0593 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0594

def B0592 : Block := .branch 170 ![590295810358705652097, 302231671076439407461890, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0593, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M7700_7900.SplitData.node0592 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0593
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0591 : Block := .branch 88 ![590295810358705652097, 302231671076439407461890, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0592]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M7700_7900.SplitData.node0591 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0592

def B0608 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M7700_7900.SplitData.node0608 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0607 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 2993155353275467247964403666759397022058098600706112] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0608, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M7700_7900.SplitData.node0607 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0608
  · rfl
  · rfl

def B0606 : Block := .branch 171 ![1496577676626844588240573268702064107938033629659521, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0607]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M7700_7900.SplitData.node0606 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0607

def B0605 : Block := .branch 170 ![590295810358705652097, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0606, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M7700_7900.SplitData.node0605 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0606
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0590 : Block := .branch 78 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0591, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0605]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M7700_7900.SplitData.node0590 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0591
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0605

theorem accepted0590 : B0590.accepted = true := by decide +kernel
theorem checked0590 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0590 (maskNeeds ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0590]
  exact B0590.sound accepted0590
#print axioms checked0590

def Tip0588_0590 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0590 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0590
def B0617 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 1511192693021931688905867091340349674550791346061376] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 821).pointIds 821), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0617 : B0617.tree = HexagonCover.NBand.M7700_7900.SplitData.node0617 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0616 : Block := .branch 170 ![748288838313422294120286634350736906063837462004097, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 820).pointIds 820), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), B0617]
theorem treeEq0616 : B0616.tree = HexagonCover.NBand.M7700_7900.SplitData.node0616 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0617

def B0615 : Block := .branch 169 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0616, (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M7700_7900.SplitData.node0615 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0616
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0614 : Block := .branch 163 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0615]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M7700_7900.SplitData.node0614 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0615

def B0613 : Block := .branch 165 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0614, (.leaf 0 [] 0)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M7700_7900.SplitData.node0613 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0614
  · rfl

def B0612 : Block := .branch 167 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0613, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M7700_7900.SplitData.node0612 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0613
  · rfl

def B0611 : Block := .branch 143 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0612, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M7700_7900.SplitData.node0611 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0612
  · rfl
  · rfl

def B0610 : Block := .branch 144 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0611, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M7700_7900.SplitData.node0610 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0611
  · rfl

def B0609 : Block := .branch 161 ![385, 216172782113785346, 9223512774343137284, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 747).pointIds 747), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0610]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M7700_7900.SplitData.node0609 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0610

def B0589 : Block := .branch 74 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0588_0590, B0609, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M7700_7900.SplitData.node0589 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0609
  · rfl
  · rfl
  · rfl

def B0626 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 1511192693021931688905867091340349674550791346061376] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 821).pointIds 821), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M7700_7900.SplitData.node0626 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0625 : Block := .branch 170 ![748288838313422294120286634350736906063837462004097, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 820).pointIds 820), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), B0626]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M7700_7900.SplitData.node0625 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0626

def B0624 : Block := .branch 169 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0625, (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M7700_7900.SplitData.node0624 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0625
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0623 : Block := .branch 163 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0624]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M7700_7900.SplitData.node0623 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0624

def B0622 : Block := .branch 165 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0623, (.leaf 0 [] 0)]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M7700_7900.SplitData.node0622 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0623
  · rfl

def B0621 : Block := .branch 167 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0622, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M7700_7900.SplitData.node0621 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0622
  · rfl

def B0620 : Block := .branch 143 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0621, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M7700_7900.SplitData.node0620 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0621
  · rfl
  · rfl

def B0619 : Block := .branch 144 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0620, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M7700_7900.SplitData.node0619 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0620
  · rfl

def B0618 : Block := .branch 161 ![385, 216172782113785346, 9223512774343137284, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 777).pointIds 777), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0619]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M7700_7900.SplitData.node0618 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0619

def B0588 : Block := .branch 73 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), B0589, B0618, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M7700_7900.SplitData.node0588 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0589
  · exact treeEq0618
  · rfl
  · rfl
  · rfl

theorem accepted0588 : B0588.accepted = true := by decide +kernel
theorem checked0588 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0588 (maskNeeds ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0588]
  exact B0588.sound accepted0588
#print axioms checked0588

end HexagonCover.NBand.M7700_7900.SplitTree.Run0007
