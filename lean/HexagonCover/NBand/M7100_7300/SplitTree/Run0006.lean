import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0000
import HexagonCover.NBand.M7100_7300.SplitTree.Run0004
import HexagonCover.NBand.M7100_7300.SplitTree.Run0005
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0027_0033 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0033 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 393248, 23384026219093785822448799774149842799085227606080] HexagonCover.NBand.M7100_7300.SplitTree.Run0000.checked0033
def Tip0027_0077 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0077 ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] HexagonCover.NBand.M7100_7300.SplitTree.Run0004.checked0077
def Tip0027_0374 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0374 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0005.checked0374
def B0032 : Block := .branch 124 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 393248, 23384026219072518174516241120183381886120742092864] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), Tip0027_0033]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M7100_7300.SplitData.node0032 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0031 : Block := .branch 150 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 23384026219072518174516241120183381886120742092864] ![(.leaf 0 (Common.fact 181).pointIds 181), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), B0032, (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M7100_7300.SplitData.node0031 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0032
  · rfl
  · rfl

def B0030 : Block := .branch 125 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 393248, 23384026219072518174516241120183381886120742092864] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), B0031, (.leaf 6 (Common.fact 180).pointIds 180)]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M7100_7300.SplitData.node0030 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0031
  · rfl

def B0029 : Block := .branch 164 ![288230376151712129, 72058693549557250, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 169).pointIds 169), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 174).pointIds 174), B0030]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M7100_7300.SplitData.node0029 := by
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
  · exact treeEq0030

def B0076 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 374144419178489218543400600972091306603544552407104] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M7100_7300.SplitData.node0076 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0075 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 374144419178489218543400600972091306603544552407104] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0076, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 375).pointIds 375)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M7100_7300.SplitData.node0075 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0076
  · rfl
  · rfl

def B0074 : Block := .branch 168 ![576460752303423873, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0075]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M7100_7300.SplitData.node0074 := by
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
  · exact treeEq0075

def B0073 : Block := .branch 59 ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![B0074, Tip0027_0077, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M7100_7300.SplitData.node0073 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0074
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0028 : Block := .branch 58 ![385, 72058693549557250, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![B0029, B0073, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M7100_7300.SplitData.node0028 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0029
  · exact treeEq0073
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0370 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M7100_7300.SplitData.node0370 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0369 : Block := .branch 168 ![288230376151712129, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0370]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M7100_7300.SplitData.node0369 := by
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
  · exact treeEq0370

def B0373 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M7100_7300.SplitData.node0373 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0372 : Block := .branch 168 ![576460752303423873, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0373]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M7100_7300.SplitData.node0372 := by
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
  · exact treeEq0373

def B0371 : Block := .branch 59 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0372, Tip0027_0374, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M7100_7300.SplitData.node0371 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0372
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0368 : Block := .branch 58 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0369, B0371, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M7100_7300.SplitData.node0368 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0369
  · exact treeEq0371
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0367 : Block := .branch 87 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), (.leaf 5 (Common.fact 133).pointIds 133), B0368]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M7100_7300.SplitData.node0367 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0368

def B0027 : Block := .branch 56 ![385, 144257025075840514, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 159).pointIds 159), B0028, B0367, (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), (.leaf 6 (Common.fact 163).pointIds 163)]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M7100_7300.SplitData.node0027 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0028
  · exact treeEq0367
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0027 : B0027.accepted = true := by decide +kernel
theorem checked0027 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0027 (maskNeeds ![385, 144257025075840514, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248]) := by
  rw [← treeEq0027]
  exact B0027.sound accepted0027
#print axioms checked0027

def B0537 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0537 : B0537.tree = HexagonCover.NBand.M7100_7300.SplitData.node0537 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0536 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0537]
theorem treeEq0536 : B0536.tree = HexagonCover.NBand.M7100_7300.SplitData.node0536 := by
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
  · exact treeEq0537

def B0535 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0536, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0535 : B0535.tree = HexagonCover.NBand.M7100_7300.SplitData.node0535 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0536
  · rfl
  · rfl

def B0534 : Block := .branch 160 ![385, 906694580884853506442754, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0535]
theorem treeEq0534 : B0534.tree = HexagonCover.NBand.M7100_7300.SplitData.node0534 := by
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
  · exact treeEq0535

def B0533 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0534, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0533 : B0533.tree = HexagonCover.NBand.M7100_7300.SplitData.node0533 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0534
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0532 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0533, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0532 : B0532.tree = HexagonCover.NBand.M7100_7300.SplitData.node0532 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0533
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0531 : Block := .branch 168 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0532, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0531 : B0531.tree = HexagonCover.NBand.M7100_7300.SplitData.node0531 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0530 : Block := .branch 163 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0531]
theorem treeEq0530 : B0530.tree = HexagonCover.NBand.M7100_7300.SplitData.node0530 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0531

def B0529 : Block := .branch 165 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0530, (.leaf 0 [] 0)]
theorem treeEq0529 : B0529.tree = HexagonCover.NBand.M7100_7300.SplitData.node0529 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0530
  · rfl

def B0528 : Block := .branch 167 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0529, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0528 : B0528.tree = HexagonCover.NBand.M7100_7300.SplitData.node0528 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0529
  · rfl

def B0527 : Block := .branch 142 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0528, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0527 : B0527.tree = HexagonCover.NBand.M7100_7300.SplitData.node0527 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0528
  · rfl
  · rfl

def B0526 : Block := .branch 144 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0527, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0526 : B0526.tree = HexagonCover.NBand.M7100_7300.SplitData.node0526 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0527
  · rfl

def B0525 : Block := .branch 170 ![385, 302231671077538919089666, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0526]
theorem treeEq0525 : B0525.tree = HexagonCover.NBand.M7100_7300.SplitData.node0525 := by
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
  · exact treeEq0526

def B0541 : Block := .branch 161 ![385, 1538, 18446884811197913092, 1496577676626844588240573307387100039795808514629640, 98320, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 871).pointIds 871), (.leaf 3 (Common.fact 667).pointIds 667), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0541 : B0541.tree = HexagonCover.NBand.M7100_7300.SplitData.node0541 := by
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

def B0540 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), B0541, (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0540 : B0540.tree = HexagonCover.NBand.M7100_7300.SplitData.node0540 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0541
  · rfl
  · rfl
  · rfl

def B0539 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0540]
theorem treeEq0539 : B0539.tree = HexagonCover.NBand.M7100_7300.SplitData.node0539 := by
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
  · exact treeEq0540

def B0538 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0539, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0538 : B0538.tree = HexagonCover.NBand.M7100_7300.SplitData.node0538 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0539
  · rfl
  · rfl

def B0524 : Block := .branch 86 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0525, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0538]
theorem treeEq0524 : B0524.tree = HexagonCover.NBand.M7100_7300.SplitData.node0524 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0525
  · rfl
  · rfl
  · exact treeEq0538

theorem accepted0524 : B0524.accepted = true := by decide +kernel
theorem checked0524 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0524 (maskNeeds ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0524]
  exact B0524.sound accepted0524
#print axioms checked0524

def B0580 : Block := .branch 79 ![374144419156732414710611177030381668558235328577921, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 717).pointIds 717), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M7100_7300.SplitData.node0580 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0579 : Block := .branch 159 ![374144419156732414710611177030381668558235328577921, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 714).pointIds 714), B0580, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0579 : B0579.tree = HexagonCover.NBand.M7100_7300.SplitData.node0579 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0580
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0578 : Block := .branch 124 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B0579, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq0578 : B0578.tree = HexagonCover.NBand.M7100_7300.SplitData.node0578 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0579
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0577 : Block := .branch 128 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0578, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0577 : B0577.tree = HexagonCover.NBand.M7100_7300.SplitData.node0577 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0578
  · rfl
  · rfl
  · rfl

def B0576 : Block := .branch 138 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0577, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0576 : B0576.tree = HexagonCover.NBand.M7100_7300.SplitData.node0576 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0577
  · rfl
  · rfl

def B0575 : Block := .branch 139 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0576, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0575 : B0575.tree = HexagonCover.NBand.M7100_7300.SplitData.node0575 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0576
  · rfl
  · rfl

def B0574 : Block := .branch 140 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0575, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0574 : B0574.tree = HexagonCover.NBand.M7100_7300.SplitData.node0574 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0575
  · rfl
  · rfl

def B0573 : Block := .branch 141 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0574, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq0573 : B0573.tree = HexagonCover.NBand.M7100_7300.SplitData.node0573 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0574
  · rfl
  · rfl

def B0572 : Block := .branch 142 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0573, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0572 : B0572.tree = HexagonCover.NBand.M7100_7300.SplitData.node0572 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0573
  · rfl
  · rfl

def B0571 : Block := .branch 165 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 840).pointIds 840), B0572, (.leaf 0 [] 0)]
theorem treeEq0571 : B0571.tree = HexagonCover.NBand.M7100_7300.SplitData.node0571 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0572
  · rfl

def B0570 : Block := .branch 167 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 839).pointIds 839), B0571, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0570 : B0570.tree = HexagonCover.NBand.M7100_7300.SplitData.node0570 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0571
  · rfl

def B0569 : Block := .branch 143 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B0570, (.leaf 5 (Common.fact 837).pointIds 837), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0569 : B0569.tree = HexagonCover.NBand.M7100_7300.SplitData.node0569 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0570
  · rfl
  · rfl

def B0568 : Block := .branch 170 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 8769009823985417509222147681923925786069185880072, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0569]
theorem treeEq0568 : B0568.tree = HexagonCover.NBand.M7100_7300.SplitData.node0568 := by
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
  · exact treeEq0569

def B0567 : Block := .branch 161 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 871).pointIds 871), B0568, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0567 : B0567.tree = HexagonCover.NBand.M7100_7300.SplitData.node0567 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0568
  · rfl
  · rfl
  · rfl

def B0566 : Block := .branch 75 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0567, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0566 : B0566.tree = HexagonCover.NBand.M7100_7300.SplitData.node0566 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0567
  · rfl
  · rfl
  · rfl
  · rfl

def B0565 : Block := .branch 162 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0566, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0565 : B0565.tree = HexagonCover.NBand.M7100_7300.SplitData.node0565 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0566
  · rfl
  · rfl
  · rfl

def B0564 : Block := .branch 172 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B0565]
theorem treeEq0564 : B0564.tree = HexagonCover.NBand.M7100_7300.SplitData.node0564 := by
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
  · exact treeEq0565

def B0563 : Block := .branch 151 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0564, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0563 : B0563.tree = HexagonCover.NBand.M7100_7300.SplitData.node0563 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0564
  · rfl
  · rfl

def B0562 : Block := .branch 132 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0563]
theorem treeEq0562 : B0562.tree = HexagonCover.NBand.M7100_7300.SplitData.node0562 := by
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
  · exact treeEq0563

def B0561 : Block := .branch 78 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B0562, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0561 : B0561.tree = HexagonCover.NBand.M7100_7300.SplitData.node0561 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0562
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0561 : B0561.accepted = true := by decide +kernel
theorem checked0561 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0561 (maskNeeds ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920]) := by
  rw [← treeEq0561]
  exact B0561.sound accepted0561
#print axioms checked0561

def Tip0552_0561 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0561 ![374144419156711147062678618376415207645270843064705, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] checked0561
def B0560 : Block := .branch 101 ![374144419156711147060143317175958748842277436653953, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![Tip0552_0561, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0560 : B0560.tree = HexagonCover.NBand.M7100_7300.SplitData.node0560 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0559 : Block := .branch 168 ![590295810358705652097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![B0560, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0559 : B0559.tree = HexagonCover.NBand.M7100_7300.SplitData.node0559 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0560
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0558 : Block := .branch 133 ![590295810358705652097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0559]
theorem treeEq0558 : B0558.tree = HexagonCover.NBand.M7100_7300.SplitData.node0558 := by
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
  · exact treeEq0559

def B0557 : Block := .branch 157 ![590295810358705652097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0558, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq0557 : B0557.tree = HexagonCover.NBand.M7100_7300.SplitData.node0557 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0558
  · rfl
  · rfl

def B0556 : Block := .branch 169 ![10384593717070245552871351364092289, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 873).pointIds 873), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B0557, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0556 : B0556.tree = HexagonCover.NBand.M7100_7300.SplitData.node0556 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0557
  · rfl

def B0589 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 855).pointIds 855), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M7100_7300.SplitData.node0589 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0588 : Block := .branch 159 ![10384593717069655257060992658440577, 737941821641931621890, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![B0589, (.leaf 1 (Common.fact 734).pointIds 734), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M7100_7300.SplitData.node0588 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0589
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0587 : Block := .branch 75 ![10384593717069655257060992658440577, 737941821641931621890, 6148, 2923003274661805836407369665432566039311865110536, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0588, (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M7100_7300.SplitData.node0587 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0588
  · rfl
  · rfl
  · rfl
  · rfl

def B0586 : Block := .branch 170 ![10384593717069655257060992658440577, 738085936830007477762, 18446884811197913092, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 850).pointIds 850), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0587]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M7100_7300.SplitData.node0586 := by
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
  · exact treeEq0587

def B0585 : Block := .branch 161 ![10384593717069655257060992658440577, 738085936830007477762, 18446884811197913092, 24584, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 871).pointIds 871), B0586, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M7100_7300.SplitData.node0585 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0586
  · rfl
  · rfl
  · rfl

def B0584 : Block := .branch 168 ![10384593717069655257060992658440577, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![B0585, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M7100_7300.SplitData.node0584 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0585
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0583 : Block := .branch 172 ![10384593717069655257060992658440577, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0584]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M7100_7300.SplitData.node0583 := by
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
  · exact treeEq0584

def B0582 : Block := .branch 171 ![10384593717069655257060992658440577, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0583, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M7100_7300.SplitData.node0582 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0583
  · rfl
  · rfl

def B0581 : Block := .branch 160 ![10384593717069655257060992658440577, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 875).pointIds 875), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0582]
theorem treeEq0581 : B0581.tree = HexagonCover.NBand.M7100_7300.SplitData.node0581 := by
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
  · exact treeEq0582

def B0555 : Block := .branch 69 ![10384593717069655257060992658440577, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0556, B0581, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0555 : B0555.tree = HexagonCover.NBand.M7100_7300.SplitData.node0555 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0556
  · exact treeEq0581
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0591 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M7100_7300.SplitData.node0591 := by
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

def B0590 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), B0591, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M7100_7300.SplitData.node0590 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0591
  · rfl
  · rfl

def B0554 : Block := .branch 68 ![10384593717069655257060992658440577, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B0555, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B0590]
theorem treeEq0554 : B0554.tree = HexagonCover.NBand.M7100_7300.SplitData.node0554 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0555
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0590

def B0553 : Block := .branch 91 ![10384593717069655257060992658440577, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0554, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0553 : B0553.tree = HexagonCover.NBand.M7100_7300.SplitData.node0553 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0554
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0552 : Block := .branch 113 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0553, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0552 : B0552.tree = HexagonCover.NBand.M7100_7300.SplitData.node0552 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0553
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0552 : B0552.accepted = true := by decide +kernel
theorem checked0552 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0552 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq0552]
  exact B0552.sound accepted0552
#print axioms checked0552

end HexagonCover.NBand.M7100_7300.SplitTree.Run0006
