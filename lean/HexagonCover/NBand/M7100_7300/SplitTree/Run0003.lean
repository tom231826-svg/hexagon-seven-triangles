import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0084_0267 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0267 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513330438687650729772168249408] HexagonCover.NBand.M7100_7300.SplitTree.Run0002.checked0267
def Tip0084_0249 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0249 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] HexagonCover.NBand.M7100_7300.SplitTree.Run0002.checked0249
def Tip0084_0085 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0085 ![385, 360289069701268994, 77937529740219874547716, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0002.checked0085
def B0266 : Block := .branch 170 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071482940061737213838602097244241984] ![(.leaf 0 (Common.fact 719).pointIds 719), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 721).pointIds 721), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), Tip0084_0267]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M7100_7300.SplitData.node0266 := by
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
  · rfl

def B0288 : Block := .branch 171 ![10384596192949733827821542456689025, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 736).pointIds 736), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 738).pointIds 738), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M7100_7300.SplitData.node0288 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0287 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 663).pointIds 663), B0288, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M7100_7300.SplitData.node0287 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0288
  · rfl
  · rfl

def B0265 : Block := .branch 86 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0266, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0287]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M7100_7300.SplitData.node0265 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0266
  · rfl
  · rfl
  · exact treeEq0287

def B0290 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M7100_7300.SplitData.node0290 := by
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

def B0289 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 663).pointIds 663), B0290, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 745).pointIds 745)]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M7100_7300.SplitData.node0289 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0290
  · rfl
  · rfl

def B0264 : Block := .branch 78 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 140).pointIds 140), B0265, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0289]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M7100_7300.SplitData.node0264 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0265
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0289

def B0248 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![Tip0084_0249, B0264, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M7100_7300.SplitData.node0248 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0264
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0292 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M7100_7300.SplitData.node0292 := by
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

def B0291 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 663).pointIds 663), B0292, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M7100_7300.SplitData.node0291 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0292
  · rfl
  · rfl

def B0247 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B0248, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B0291]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M7100_7300.SplitData.node0247 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0248
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0291

def B0246 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0247, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M7100_7300.SplitData.node0246 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0245 : Block := .branch 113 ![385, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0246, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M7100_7300.SplitData.node0245 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0246
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 76 ![385, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), Tip0084_0085, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B0245]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M7100_7300.SplitData.node0084 := by
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
  · exact treeEq0245

theorem accepted0084 : B0084.accepted = true := by decide +kernel
theorem checked0084 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0084 (maskNeeds ![385, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0084]
  exact B0084.sound accepted0084
#print axioms checked0084

def Tip0083_0084 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0084 ![385, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0084
def B0305 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7495311147073313687490538190474628173199236054646848] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 770).pointIds 770)]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M7100_7300.SplitData.node0305 := by
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

def B0304 : Block := .branch 172 ![385, 147646011283225970178, 11842809695321532143620, 38704515693599612171477000, 2993155358828875476113802322786877192417440224608272, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 767).pointIds 767), (.leaf 3 (Common.fact 768).pointIds 768), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0305]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M7100_7300.SplitData.node0304 := by
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
  · exact treeEq0305

def B0303 : Block := .branch 171 ![385, 147646011283225970178, 11842809695321532143620, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), B0304, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M7100_7300.SplitData.node0303 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0304
  · rfl
  · rfl

def B0302 : Block := .branch 159 ![374144419156732414708075875829334913944883216515457, 604610555818597813323266, 11842809695321532143620, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 760).pointIds 760), (.leaf 1 (Common.fact 761).pointIds 761), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0303]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M7100_7300.SplitData.node0302 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0303

def B0301 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147646011283225970178, 11842809695321532143620, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0302, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M7100_7300.SplitData.node0301 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0302
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0300 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147646011283225970178, 11842809695321532143620, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0301, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M7100_7300.SplitData.node0300 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0301
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0299 : Block := .branch 168 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0300, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M7100_7300.SplitData.node0299 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0298 : Block := .branch 163 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0299]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M7100_7300.SplitData.node0298 := by
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
  · exact treeEq0299

def B0297 : Block := .branch 165 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0298, (.leaf 0 [] 0)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M7100_7300.SplitData.node0297 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0298
  · rfl

def B0296 : Block := .branch 167 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0297, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M7100_7300.SplitData.node0296 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0297
  · rfl

def B0295 : Block := .branch 142 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0296, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M7100_7300.SplitData.node0295 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0296
  · rfl
  · rfl

def B0294 : Block := .branch 144 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0295, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M7100_7300.SplitData.node0294 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0295
  · rfl

def B0293 : Block := .branch 170 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 752).pointIds 752), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0294]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M7100_7300.SplitData.node0293 := by
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
  · exact treeEq0294

def B0083 : Block := .branch 74 ![385, 147934241659377681922, 11861292468192260659204, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0083_0084, B0293, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M7100_7300.SplitData.node0083 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0293
  · rfl
  · rfl
  · rfl

theorem accepted0083 : B0083.accepted = true := by decide +kernel
theorem checked0083 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0083 (maskNeeds ![385, 147934241659377681922, 11861292468192260659204, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0083]
  exact B0083.sound accepted0083
#print axioms checked0083

def Tip0082_0083 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0083 ![385, 147934241659377681922, 11861292468192260659204, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0083
def B0318 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7495311147073313687490538190474628173199236054646848] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 770).pointIds 770)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M7100_7300.SplitData.node0318 := by
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

def B0317 : Block := .branch 172 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 2993155358828875476113802322786877192417440224608272, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0318]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M7100_7300.SplitData.node0317 := by
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
  · exact treeEq0318

def B0316 : Block := .branch 171 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 773).pointIds 773), (.leaf 3 (Common.fact 774).pointIds 774), B0317, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M7100_7300.SplitData.node0316 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0317
  · rfl
  · rfl

def B0315 : Block := .branch 159 ![374144419156732414708075875829334913944883216515457, 604610555818597813323266, 7120443212451886929924, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 760).pointIds 760), (.leaf 1 (Common.fact 761).pointIds 761), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0316]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M7100_7300.SplitData.node0315 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0316

def B0314 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0315, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M7100_7300.SplitData.node0314 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0315
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0313 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0314, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M7100_7300.SplitData.node0313 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0312 : Block := .branch 168 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0313, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M7100_7300.SplitData.node0312 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0313
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0311 : Block := .branch 163 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0312]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M7100_7300.SplitData.node0311 := by
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
  · exact treeEq0312

def B0310 : Block := .branch 165 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0311, (.leaf 0 [] 0)]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M7100_7300.SplitData.node0310 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0311
  · rfl

def B0309 : Block := .branch 167 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0310, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M7100_7300.SplitData.node0309 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0310
  · rfl

def B0308 : Block := .branch 142 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0309, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M7100_7300.SplitData.node0308 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0309
  · rfl
  · rfl

def B0307 : Block := .branch 144 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0308, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M7100_7300.SplitData.node0307 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0308
  · rfl

def B0306 : Block := .branch 170 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 771).pointIds 771), (.leaf 3 (Common.fact 772).pointIds 772), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0307]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M7100_7300.SplitData.node0306 := by
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
  · exact treeEq0307

def B0082 : Block := .branch 73 ![385, 147934241659377681922, 7138925985322615445508, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0082_0083, B0306, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M7100_7300.SplitData.node0082 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0306
  · rfl
  · rfl
  · rfl

theorem accepted0082 : B0082.accepted = true := by decide +kernel
theorem checked0082 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0082 (maskNeeds ![385, 147934241659377681922, 7138925985322615445508, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0082]
  exact B0082.sound accepted0082
#print axioms checked0082

def Tip0081_0082 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0082 ![385, 147934241659377681922, 7138925985322615445508, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0082
def B0331 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7495311147073313687490538190474628173199236054646848] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 770).pointIds 770)]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M7100_7300.SplitData.node0331 := by
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

def B0330 : Block := .branch 172 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 2993155358828875476113802322786877192417440224608272, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 781).pointIds 781), (.leaf 3 (Common.fact 782).pointIds 782), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0331]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M7100_7300.SplitData.node0330 := by
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
  · exact treeEq0331

def B0329 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B0330, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M7100_7300.SplitData.node0329 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl
  · rfl

def B0328 : Block := .branch 159 ![374144419156732414708075875829334913944883216515457, 604610555818597813323266, 2398076729582241716228, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 760).pointIds 760), (.leaf 1 (Common.fact 761).pointIds 761), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0329]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M7100_7300.SplitData.node0328 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0329

def B0327 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0328, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M7100_7300.SplitData.node0327 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0328
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0326 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0327, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M7100_7300.SplitData.node0326 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0327
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0325 : Block := .branch 168 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0326, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M7100_7300.SplitData.node0325 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0326
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0324 : Block := .branch 163 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0325]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M7100_7300.SplitData.node0324 := by
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
  · exact treeEq0325

def B0323 : Block := .branch 165 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0324, (.leaf 0 [] 0)]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M7100_7300.SplitData.node0323 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl

def B0322 : Block := .branch 167 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0323, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M7100_7300.SplitData.node0322 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0323
  · rfl

def B0321 : Block := .branch 142 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0322, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M7100_7300.SplitData.node0321 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0322
  · rfl
  · rfl

def B0320 : Block := .branch 144 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0321, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M7100_7300.SplitData.node0320 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl

def B0319 : Block := .branch 170 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0320]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M7100_7300.SplitData.node0319 := by
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
  · exact treeEq0320

def B0081 : Block := .branch 72 ![385, 147934241659377681922, 2416559502452970231812, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip0081_0082, B0319, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M7100_7300.SplitData.node0081 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0319
  · rfl
  · rfl
  · rfl

theorem accepted0081 : B0081.accepted = true := by decide +kernel
theorem checked0081 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0081 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0081]
  exact B0081.sound accepted0081
#print axioms checked0081

def Tip0078_0081 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0081 ![385, 147934241659377681922, 2416559502452970231812, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0081
def B0344 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7495311147073313687490538190474628173199236054646848] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 770).pointIds 770)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M7100_7300.SplitData.node0344 := by
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

def B0343 : Block := .branch 172 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 2993155358828875476113802322786877192417440224608272, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 787).pointIds 787), (.leaf 3 (Common.fact 788).pointIds 788), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0344]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M7100_7300.SplitData.node0343 := by
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
  · exact treeEq0344

def B0342 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 393248, 1509000440565935334528245115668732924688536358617152] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 785).pointIds 785), (.leaf 3 (Common.fact 786).pointIds 786), B0343, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M7100_7300.SplitData.node0342 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0343
  · rfl
  · rfl

def B0341 : Block := .branch 159 ![374144419156732414708075875829334913944883216515457, 604610555818597813323266, 36893488147419109380, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 760).pointIds 760), (.leaf 1 (Common.fact 761).pointIds 761), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0342]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M7100_7300.SplitData.node0341 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342

def B0340 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0341, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M7100_7300.SplitData.node0340 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0341
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0339 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0340, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M7100_7300.SplitData.node0339 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0340
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0338 : Block := .branch 168 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0339, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M7100_7300.SplitData.node0338 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0339
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0337 : Block := .branch 163 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0338]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M7100_7300.SplitData.node0337 := by
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
  · exact treeEq0338

def B0336 : Block := .branch 165 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0337, (.leaf 0 [] 0)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M7100_7300.SplitData.node0336 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl

def B0335 : Block := .branch 167 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0336, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M7100_7300.SplitData.node0335 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0336
  · rfl

def B0334 : Block := .branch 142 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0335, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M7100_7300.SplitData.node0334 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl
  · rfl

def B0333 : Block := .branch 144 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0334, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M7100_7300.SplitData.node0333 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0334
  · rfl

def B0332 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 783).pointIds 783), (.leaf 3 (Common.fact 784).pointIds 784), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0333]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M7100_7300.SplitData.node0332 := by
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
  · exact treeEq0333

def B0080 : Block := .branch 71 ![385, 147934241659377681922, 55376261018147624964, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip0078_0081, B0332, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M7100_7300.SplitData.node0080 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0332
  · rfl
  · rfl
  · rfl

def B0348 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M7100_7300.SplitData.node0348 := by
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

def B0347 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0348, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 791).pointIds 791)]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M7100_7300.SplitData.node0347 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0348
  · rfl
  · rfl

def B0346 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0347, (.leaf 6 (Common.fact 790).pointIds 790)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M7100_7300.SplitData.node0346 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0347
  · rfl

def B0345 : Block := .branch 168 ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054365516851681135427648] ![B0346, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 789).pointIds 789)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M7100_7300.SplitData.node0345 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0346
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0079 : Block := .branch 67 ![385, 360289069701268994, 55376261018147624964, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 378).pointIds 378), B0080, (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B0345]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M7100_7300.SplitData.node0079 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0080
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345

def B0078 : Block := .branch 87 ![385, 360289069701268994, 55376261018147624964, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), (.leaf 5 (Common.fact 133).pointIds 133), B0079]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M7100_7300.SplitData.node0078 := by
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
  · exact treeEq0079

theorem accepted0078 : B0078.accepted = true := by decide +kernel
theorem checked0078 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0078 (maskNeeds ![385, 360289069701268994, 55376261018147624964, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248]) := by
  rw [← treeEq0078]
  exact B0078.sound accepted0078
#print axioms checked0078

end HexagonCover.NBand.M7100_7300.SplitTree.Run0003
