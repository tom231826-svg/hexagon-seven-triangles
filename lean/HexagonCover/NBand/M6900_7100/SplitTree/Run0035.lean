import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0000
import HexagonCover.NBand.M6900_7100.SplitTree.Run0033
import HexagonCover.NBand.M6900_7100.SplitTree.Run0034
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0035
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2461_2528 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2528 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0034.checked2528
def Tip2461_2465 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2465 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0034.checked2465
def Tip2461_2555 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2555 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0034.checked2555
def Tip2461_2568 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2568 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0034.checked2568
def Tip2461_2581 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2581 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0034.checked2581
def B2554 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq2554 : B2554.tree = HexagonCover.NBand.M6900_7100.SplitData.node2554 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2553 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2554, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq2553 : B2553.tree = HexagonCover.NBand.M6900_7100.SplitData.node2553 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2554
  · rfl
  · rfl

def B2552 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 737869904785382049282, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1091).pointIds 1091), (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2553]
theorem treeEq2552 : B2552.tree = HexagonCover.NBand.M6900_7100.SplitData.node2552 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2553

def B2551 : Block := .branch 171 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 1461501659108974401460659219987178972127352586304] ![B2552, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq2551 : B2551.tree = HexagonCover.NBand.M6900_7100.SplitData.node2551 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2552
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2550 : Block := .branch 151 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2551, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2550 : B2550.tree = HexagonCover.NBand.M6900_7100.SplitData.node2550 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2551
  · rfl

def B2549 : Block := .branch 170 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2550, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1089).pointIds 1089)]
theorem treeEq2549 : B2549.tree = HexagonCover.NBand.M6900_7100.SplitData.node2549 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2550
  · rfl
  · rfl

def B2548 : Block := .branch 160 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1088).pointIds 1088), (.leaf 2 (Common.fact 1084).pointIds 1084), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2549]
theorem treeEq2548 : B2548.tree = HexagonCover.NBand.M6900_7100.SplitData.node2548 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2549

def B2527 : Block := .branch 69 ![10384596192949733827821542456689025, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip2461_2528, B2548, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq2527 : B2527.tree = HexagonCover.NBand.M6900_7100.SplitData.node2527 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2548
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2526 : Block := .branch 91 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B2527, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq2526 : B2526.tree = HexagonCover.NBand.M6900_7100.SplitData.node2526 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2527
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2464 : Block := .branch 76 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip2461_2465, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B2526]
theorem treeEq2464 : B2464.tree = HexagonCover.NBand.M6900_7100.SplitData.node2464 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2526

def B2463 : Block := .branch 74 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B2464, Tip2461_2555, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2463 : B2463.tree = HexagonCover.NBand.M6900_7100.SplitData.node2463 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2464
  · rfl
  · rfl
  · rfl
  · rfl

def B2462 : Block := .branch 73 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B2463, Tip2461_2568, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2462 : B2462.tree = HexagonCover.NBand.M6900_7100.SplitData.node2462 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2463
  · rfl
  · rfl
  · rfl
  · rfl

def B2461 : Block := .branch 72 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B2462, Tip2461_2581, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2461 : B2461.tree = HexagonCover.NBand.M6900_7100.SplitData.node2461 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2462
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2461 : B2461.accepted = true := by decide +kernel
theorem checked2461 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2461 (maskNeeds ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2461]
  exact B2461.sound accepted2461
#print axioms checked2461

def B2615 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676637733623982043299532301799565491506872336, 393248, 7132127990196584312316922045317412258702313083371584] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 1116).pointIds 1116), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 1117).pointIds 1117)]
theorem treeEq2615 : B2615.tree = HexagonCover.NBand.M6900_7100.SplitData.node2615 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2614 : Block := .branch 133 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 7132127990196584312316922045317412258702313083371584] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), B2615, (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 1115).pointIds 1115)]
theorem treeEq2614 : B2614.tree = HexagonCover.NBand.M6900_7100.SplitData.node2614 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2615
  · rfl
  · rfl

def B2613 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 737869904785382049282, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196635410966675352638475621367872] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1091).pointIds 1091), (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2614]
theorem treeEq2613 : B2613.tree = HexagonCover.NBand.M6900_7100.SplitData.node2613 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2614

def B2612 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 147574094426676397570, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952478359237320661384159559744] ![(.leaf 0 (Common.fact 1073).pointIds 1073), B2613, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1114).pointIds 1114)]
theorem treeEq2612 : B2612.tree = HexagonCover.NBand.M6900_7100.SplitData.node2612 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2613
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2611 : Block := .branch 71 ![2993155353253689176481146537402947624255349848015233, 147574094426676397570, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952478359237320661384159559744] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B2612, (.leaf 3 (Common.fact 1113).pointIds 1113), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq2611 : B2611.tree = HexagonCover.NBand.M6900_7100.SplitData.node2611 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2612
  · rfl
  · rfl
  · rfl
  · rfl

def B2610 : Block := .branch 72 ![2993155353253689176481146537402947624255349848015233, 147574094426676397570, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B2611, (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2610 : B2610.tree = HexagonCover.NBand.M6900_7100.SplitData.node2610 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2611
  · rfl
  · rfl
  · rfl
  · rfl

def B2609 : Block := .branch 73 ![2993155353253689176481146537402947624255349848015233, 147574094426676397570, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B2610, (.leaf 3 (Common.fact 1111).pointIds 1111), (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2609 : B2609.tree = HexagonCover.NBand.M6900_7100.SplitData.node2609 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2610
  · rfl
  · rfl
  · rfl
  · rfl

def B2608 : Block := .branch 74 ![2993155353253689176481146537402947624255349848015233, 147574094426676397570, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B2609, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2608 : B2608.tree = HexagonCover.NBand.M6900_7100.SplitData.node2608 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2609
  · rfl
  · rfl
  · rfl
  · rfl

def B2607 : Block := .branch 75 ![2993155353253689176481146537402947624255349848015233, 147574094426676397570, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B2608, (.leaf 3 (Common.fact 1109).pointIds 1109), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 1110).pointIds 1110)]
theorem treeEq2607 : B2607.tree = HexagonCover.NBand.M6900_7100.SplitData.node2607 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2608
  · rfl
  · rfl
  · rfl
  · rfl

def B2606 : Block := .branch 172 ![2993155353253689176481146537402947624255349848015233, 147718209614752253442, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2607]
theorem treeEq2606 : B2606.tree = HexagonCover.NBand.M6900_7100.SplitData.node2606 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2607

def B2605 : Block := .branch 161 ![2993155353253689176481146537402947624255349848015233, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), B2606, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1108).pointIds 1108)]
theorem treeEq2605 : B2605.tree = HexagonCover.NBand.M6900_7100.SplitData.node2605 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2606
  · rfl
  · rfl
  · rfl

def B2604 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2605]
theorem treeEq2604 : B2604.tree = HexagonCover.NBand.M6900_7100.SplitData.node2604 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2605

def B2603 : Block := .branch 171 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![B2604, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq2603 : B2603.tree = HexagonCover.NBand.M6900_7100.SplitData.node2603 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2604
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2602 : Block := .branch 151 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2603, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2602 : B2602.tree = HexagonCover.NBand.M6900_7100.SplitData.node2602 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2603
  · rfl

def B2601 : Block := .branch 170 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2602, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq2601 : B2601.tree = HexagonCover.NBand.M6900_7100.SplitData.node2601 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2602
  · rfl
  · rfl

theorem accepted2601 : B2601.accepted = true := by decide +kernel
theorem checked2601 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2601 (maskNeeds ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488]) := by
  rw [← treeEq2601]
  exact B2601.sound accepted2601
#print axioms checked2601

def Tip2458_2461 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2461 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2461
def Tip2458_2601 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2601 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] checked2601
def B2600 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906205674461988354, 6148, 24584, 98320, 393248, 377067422453151024379807970637523872642856417493056] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq2600 : B2600.tree = HexagonCover.NBand.M6900_7100.SplitData.node2600 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2599 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 400451448650445471071066927960984400957351338180672] ![(.leaf 0 (Common.fact 928).pointIds 928), B2600, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1104).pointIds 1104)]
theorem treeEq2599 : B2599.tree = HexagonCover.NBand.M6900_7100.SplitData.node2599 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2600
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2598 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379807970637523872642856417493056] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2599]
theorem treeEq2598 : B2598.tree = HexagonCover.NBand.M6900_7100.SplitData.node2598 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2599

def B2597 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 377067422453151024379807970637523872642856417493056] ![B2598, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq2597 : B2597.tree = HexagonCover.NBand.M6900_7100.SplitData.node2597 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2598
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2596 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2597, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2596 : B2596.tree = HexagonCover.NBand.M6900_7100.SplitData.node2596 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2597
  · rfl

def B2595 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2596, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq2595 : B2595.tree = HexagonCover.NBand.M6900_7100.SplitData.node2595 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2596
  · rfl
  · rfl

def B2594 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), B2595]
theorem treeEq2594 : B2594.tree = HexagonCover.NBand.M6900_7100.SplitData.node2594 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2595

def B2460 : Block := .branch 71 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip2458_2461, B2594, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq2460 : B2460.tree = HexagonCover.NBand.M6900_7100.SplitData.node2460 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2594
  · rfl
  · rfl
  · rfl

def B2459 : Block := .branch 68 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B2460, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), Tip2458_2601]
theorem treeEq2459 : B2459.tree = HexagonCover.NBand.M6900_7100.SplitData.node2459 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2460
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2621 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906205674461988354, 6148, 24584, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1121).pointIds 1121)]
theorem treeEq2621 : B2621.tree = HexagonCover.NBand.M6900_7100.SplitData.node2621 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2620 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 397528445375783665234659403553194498198094787117120] ![(.leaf 0 (Common.fact 928).pointIds 928), B2621, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq2620 : B2620.tree = HexagonCover.NBand.M6900_7100.SplitData.node2620 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2621
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2619 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2620]
theorem treeEq2619 : B2619.tree = HexagonCover.NBand.M6900_7100.SplitData.node2619 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2620

def B2618 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400446229733969883599866429504] ![B2619, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq2618 : B2618.tree = HexagonCover.NBand.M6900_7100.SplitData.node2618 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2619
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2617 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2618, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2617 : B2617.tree = HexagonCover.NBand.M6900_7100.SplitData.node2617 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2618
  · rfl

def B2616 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2617, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq2616 : B2616.tree = HexagonCover.NBand.M6900_7100.SplitData.node2616 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2617
  · rfl
  · rfl

def B2458 : Block := .branch 67 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 439).pointIds 439), B2459, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), B2616]
theorem treeEq2458 : B2458.tree = HexagonCover.NBand.M6900_7100.SplitData.node2458 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2459
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2616

theorem accepted2458 : B2458.accepted = true := by decide +kernel
theorem checked2458 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2458 (maskNeeds ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2458]
  exact B2458.sound accepted2458
#print axioms checked2458

def Tip0028_0036 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0036 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0000.checked0036
def Tip0028_0076 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0076 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0033.checked0076
def Tip0028_2458 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2458 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2458
def B0035 : Block := .branch 157 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), Tip0028_0036, (.leaf 5 (Common.fact 209).pointIds 209), (.leaf 0 [] 0)]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M6900_7100.SplitData.node0035 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0034 : Block := .branch 166 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778072132294545856081217810472224948288] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), B0035, (.leaf 6 (Common.fact 204).pointIds 204)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M6900_7100.SplitData.node0034 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0035
  · rfl

def B0033 : Block := .branch 109 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0034]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M6900_7100.SplitData.node0033 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0034

def B0032 : Block := .branch 150 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 98320, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0033, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M6900_7100.SplitData.node0032 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0033
  · rfl
  · rfl

def B0031 : Block := .branch 125 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 181).pointIds 181), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0032, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M6900_7100.SplitData.node0031 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0032
  · rfl

def B0030 : Block := .branch 164 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0031]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M6900_7100.SplitData.node0030 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0031

def B0029 : Block := .branch 58 ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0030, Tip0028_0076, (.leaf 2 (Common.fact 170).pointIds 170), (.leaf 3 (Common.fact 171).pointIds 171), (.leaf 4 (Common.fact 172).pointIds 172), (.leaf 5 (Common.fact 173).pointIds 173), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M6900_7100.SplitData.node0029 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0030
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2626 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906205674461988354, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1124).pointIds 1124)]
theorem treeEq2626 : B2626.tree = HexagonCover.NBand.M6900_7100.SplitData.node2626 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2625 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), B2626, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq2625 : B2625.tree = HexagonCover.NBand.M6900_7100.SplitData.node2625 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2626
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2624 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B2625, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq2624 : B2624.tree = HexagonCover.NBand.M6900_7100.SplitData.node2624 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2625
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2623 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2624, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2623 : B2623.tree = HexagonCover.NBand.M6900_7100.SplitData.node2623 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2624
  · rfl

def B2622 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2623, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq2622 : B2622.tree = HexagonCover.NBand.M6900_7100.SplitData.node2622 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2623
  · rfl
  · rfl

def B2457 : Block := .branch 65 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), Tip0028_2458, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B2622]
theorem treeEq2457 : B2457.tree = HexagonCover.NBand.M6900_7100.SplitData.node2457 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2622

def B2456 : Block := .branch 59 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 390).pointIds 390), B2457, (.leaf 2 (Common.fact 378).pointIds 378), (.leaf 3 (Common.fact 379).pointIds 379), (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2456 : B2456.tree = HexagonCover.NBand.M6900_7100.SplitData.node2456 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2457
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2455 : Block := .branch 113 ![385, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2456, (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2455 : B2455.tree = HexagonCover.NBand.M6900_7100.SplitData.node2455 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2456
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2454 : Block := .branch 168 ![385, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 1042).pointIds 1042), (.leaf 2 (Common.fact 1043).pointIds 1043), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2455]
theorem treeEq2454 : B2454.tree = HexagonCover.NBand.M6900_7100.SplitData.node2454 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2455

def B0028 : Block := .branch 56 ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 165).pointIds 165), B0029, B2454, (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), (.leaf 6 (Common.fact 169).pointIds 169)]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M6900_7100.SplitData.node0028 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0029
  · exact treeEq2454
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0028 : B0028.accepted = true := by decide +kernel
theorem checked0028 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0028 (maskNeeds ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0028]
  exact B0028.sound accepted0028
#print axioms checked0028

def B2649 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq2649 : B2649.tree = HexagonCover.NBand.M6900_7100.SplitData.node2649 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2648 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2649, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq2648 : B2648.tree = HexagonCover.NBand.M6900_7100.SplitData.node2648 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2649
  · rfl
  · rfl
  · rfl

def B2647 : Block := .branch 142 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B2648]
theorem treeEq2647 : B2647.tree = HexagonCover.NBand.M6900_7100.SplitData.node2647 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2648

def B2646 : Block := .branch 166 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B2647, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2646 : B2646.tree = HexagonCover.NBand.M6900_7100.SplitData.node2646 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2647
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2645 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B2646, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2645 : B2645.tree = HexagonCover.NBand.M6900_7100.SplitData.node2645 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2646
  · rfl

def B2658 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1058).pointIds 1058)]
theorem treeEq2658 : B2658.tree = HexagonCover.NBand.M6900_7100.SplitData.node2658 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2657 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2658, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq2657 : B2657.tree = HexagonCover.NBand.M6900_7100.SplitData.node2657 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2658
  · rfl
  · rfl
  · rfl

def B2656 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 186255823898127764478106319013159115297948532752, 393248, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2657]
theorem treeEq2656 : B2656.tree = HexagonCover.NBand.M6900_7100.SplitData.node2656 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2657

def B2655 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2656, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2655 : B2655.tree = HexagonCover.NBand.M6900_7100.SplitData.node2655 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2656
  · rfl
  · rfl

def B2654 : Block := .branch 132 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B2655]
theorem treeEq2654 : B2654.tree = HexagonCover.NBand.M6900_7100.SplitData.node2654 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2655

def B2653 : Block := .branch 133 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B2654]
theorem treeEq2653 : B2653.tree = HexagonCover.NBand.M6900_7100.SplitData.node2653 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2654

def B2652 : Block := .branch 157 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2653, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq2652 : B2652.tree = HexagonCover.NBand.M6900_7100.SplitData.node2652 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2653
  · rfl
  · rfl

def B2651 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2652, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq2651 : B2651.tree = HexagonCover.NBand.M6900_7100.SplitData.node2651 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2652
  · rfl

def B2650 : Block := .branch 169 ![10387129018270111715863986064851329, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B2651, (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq2650 : B2650.tree = HexagonCover.NBand.M6900_7100.SplitData.node2650 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2651
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2644 : Block := .branch 108 ![10387129018270111715863986064851329, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2645, (.leaf 5 (Common.fact 322).pointIds 322), B2650]
theorem treeEq2644 : B2644.tree = HexagonCover.NBand.M6900_7100.SplitData.node2644 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2645
  · rfl
  · exact treeEq2650

theorem accepted2644 : B2644.accepted = true := by decide +kernel
theorem checked2644 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2644 (maskNeeds ![10387129018270111715863986064851329, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2644]
  exact B2644.sound accepted2644
#print axioms checked2644

end HexagonCover.NBand.M6900_7100.SplitTree.Run0035
