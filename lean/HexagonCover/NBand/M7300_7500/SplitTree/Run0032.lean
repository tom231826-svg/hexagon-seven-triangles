import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0002
import HexagonCover.NBand.M7300_7500.SplitTree.Run0003
import HexagonCover.NBand.M7300_7500.SplitTree.Run0005
import HexagonCover.NBand.M7300_7500.SplitTree.Run0009
import HexagonCover.NBand.M7300_7500.SplitTree.Run0016
import HexagonCover.NBand.M7300_7500.SplitTree.Run0030
import HexagonCover.NBand.M7300_7500.SplitTree.Run0031
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0032
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip1765_2236 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2236 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0030.checked2236
def Tip1765_2162 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2162 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0031.checked2162
def Tip1765_2030 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2030 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0031.checked2030
def Tip1765_1766 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1766 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0031.checked1766
def B2235 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq2235 : B2235.tree = HexagonCover.NBand.M7300_7500.SplitData.node2235 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2234 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2235]
theorem treeEq2234 : B2234.tree = HexagonCover.NBand.M7300_7500.SplitData.node2234 := by
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
  · exact treeEq2235

def B2233 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), B2234, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2233 : B2233.tree = HexagonCover.NBand.M7300_7500.SplitData.node2233 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2234
  · rfl
  · rfl

def B2232 : Block := .branch 169 ![10384593717070245552871351364092289, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), B2233, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2232 : B2232.tree = HexagonCover.NBand.M7300_7500.SplitData.node2232 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2233
  · rfl

def B2231 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2232, Tip1765_2236, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2231 : B2231.tree = HexagonCover.NBand.M7300_7500.SplitData.node2231 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2232
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2291 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq2291 : B2291.tree = HexagonCover.NBand.M7300_7500.SplitData.node2291 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2290 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B2291, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq2290 : B2290.tree = HexagonCover.NBand.M7300_7500.SplitData.node2290 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2291
  · rfl
  · rfl

def B2289 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2290]
theorem treeEq2289 : B2289.tree = HexagonCover.NBand.M7300_7500.SplitData.node2289 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2290

def B2288 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B2289, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2288 : B2288.tree = HexagonCover.NBand.M7300_7500.SplitData.node2288 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2287 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B2288, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2287 : B2287.tree = HexagonCover.NBand.M7300_7500.SplitData.node2287 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2288
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2286 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2287]
theorem treeEq2286 : B2286.tree = HexagonCover.NBand.M7300_7500.SplitData.node2286 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2287

def B2285 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B2286, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2285 : B2285.tree = HexagonCover.NBand.M7300_7500.SplitData.node2285 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2286
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2284 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2285, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2284 : B2284.tree = HexagonCover.NBand.M7300_7500.SplitData.node2284 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2285
  · rfl

def B2283 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2284, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq2283 : B2283.tree = HexagonCover.NBand.M7300_7500.SplitData.node2283 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2284
  · rfl
  · rfl

def B2230 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), B2231, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B2283]
theorem treeEq2230 : B2230.tree = HexagonCover.NBand.M7300_7500.SplitData.node2230 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2231
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2283

def B2229 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2230, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2229 : B2229.tree = HexagonCover.NBand.M7300_7500.SplitData.node2229 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2230
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2228 : Block := .branch 113 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2229, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2228 : B2228.tree = HexagonCover.NBand.M7300_7500.SplitData.node2228 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2229
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2161 : Block := .branch 76 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip1765_2162, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B2228]
theorem treeEq2161 : B2161.tree = HexagonCover.NBand.M7300_7500.SplitData.node2161 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2228

def B2029 : Block := .branch 74 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip1765_2030, B2161, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq2029 : B2029.tree = HexagonCover.NBand.M7300_7500.SplitData.node2029 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2161
  · rfl
  · rfl
  · rfl

def B1765 : Block := .branch 73 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip1765_1766, B2029, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq1765 : B1765.tree = HexagonCover.NBand.M7300_7500.SplitData.node1765 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2029
  · rfl
  · rfl
  · rfl

theorem accepted1765 : B1765.accepted = true := by decide +kernel
theorem checked1765 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1765 (maskNeeds ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq1765]
  exact B1765.sound accepted1765
#print axioms checked1765

def Tip0081_0086 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0086 ![385, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0002.checked0086
def Tip0081_0239 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0239 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] HexagonCover.NBand.M7300_7500.SplitTree.Run0003.checked0239
def Tip0081_0316 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0316 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0005.checked0316
def Tip0081_0447 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0447 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0009.checked0447
def Tip0081_0710 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0710 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0016.checked0710
def B0235 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 152).pointIds 152)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M7300_7500.SplitData.node0235 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0234 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0235, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 145).pointIds 145)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M7300_7500.SplitData.node0234 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0235
  · rfl
  · rfl

def B0233 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B0234, (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M7300_7500.SplitData.node0233 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl

def B0085 : Block := .branch 78 ![385, 360289069701268994, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip0081_0086, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0233]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M7300_7500.SplitData.node0085 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0233

def B0315 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5316911983139663491615228241121476624, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 725).pointIds 725), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M7300_7500.SplitData.node0315 := by
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

def B0314 : Block := .branch 122 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), B0315, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M7300_7500.SplitData.node0314 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0315
  · rfl
  · rfl

def B0313 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0314]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M7300_7500.SplitData.node0313 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0314

def B0312 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B0313, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M7300_7500.SplitData.node0312 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0313
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0311 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B0312, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M7300_7500.SplitData.node0311 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0312
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0310 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0311]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M7300_7500.SplitData.node0310 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0311

def B0309 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![B0310, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M7300_7500.SplitData.node0309 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0310
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0308 : Block := .branch 170 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B0309, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M7300_7500.SplitData.node0308 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0309
  · rfl

def B0307 : Block := .branch 171 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), B0308, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M7300_7500.SplitData.node0307 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0308
  · rfl
  · rfl

def B0238 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip0081_0239, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B0307]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M7300_7500.SplitData.node0238 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0307

def B0237 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![B0238, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M7300_7500.SplitData.node0237 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0238
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0236 : Block := .branch 113 ![385, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![B0237, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M7300_7500.SplitData.node0236 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0237
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 76 ![385, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B0085, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B0236]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M7300_7500.SplitData.node0084 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0085
  · rfl
  · rfl
  · rfl
  · exact treeEq0236

def B0083 : Block := .branch 74 ![385, 147934241659377681922, 11861292468192260659204, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), B0084, Tip0081_0316, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M7300_7500.SplitData.node0083 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0084
  · rfl
  · rfl
  · rfl
  · rfl

def B0082 : Block := .branch 73 ![385, 147934241659377681922, 7138925985322615445508, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), B0083, Tip0081_0447, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M7300_7500.SplitData.node0082 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0083
  · rfl
  · rfl
  · rfl
  · rfl

def B0081 : Block := .branch 72 ![385, 147934241659377681922, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B0082, Tip0081_0710, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M7300_7500.SplitData.node0081 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0082
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0081 : B0081.accepted = true := by decide +kernel
theorem checked0081 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0081 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq0081]
  exact B0081.sound accepted0081
#print axioms checked0081

def B2317 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 797).pointIds 797), (.leaf 1 (Common.fact 677).pointIds 677), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 798).pointIds 798)]
theorem treeEq2317 : B2317.tree = HexagonCover.NBand.M7300_7500.SplitData.node2317 := by
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

def B2316 : Block := .branch 159 ![374144419156732414708075875829334913944883216515457, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 795).pointIds 795), B2317, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq2316 : B2316.tree = HexagonCover.NBand.M7300_7500.SplitData.node2316 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2317
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2315 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![B2316, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 794).pointIds 794)]
theorem treeEq2315 : B2315.tree = HexagonCover.NBand.M7300_7500.SplitData.node2315 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2316
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2314 : Block := .branch 138 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B2315, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2314 : B2314.tree = HexagonCover.NBand.M7300_7500.SplitData.node2314 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2315
  · rfl
  · rfl

def B2313 : Block := .branch 139 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B2314, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq2313 : B2313.tree = HexagonCover.NBand.M7300_7500.SplitData.node2313 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2314
  · rfl
  · rfl

def B2312 : Block := .branch 140 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B2313, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 791).pointIds 791)]
theorem treeEq2312 : B2312.tree = HexagonCover.NBand.M7300_7500.SplitData.node2312 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2313
  · rfl
  · rfl

def B2311 : Block := .branch 141 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B2312, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 790).pointIds 790)]
theorem treeEq2311 : B2311.tree = HexagonCover.NBand.M7300_7500.SplitData.node2311 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2312
  · rfl
  · rfl

def B2310 : Block := .branch 142 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2311, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 789).pointIds 789)]
theorem treeEq2310 : B2310.tree = HexagonCover.NBand.M7300_7500.SplitData.node2310 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2311
  · rfl
  · rfl

def B2309 : Block := .branch 68 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 787).pointIds 787), B2310, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), (.leaf 6 (Common.fact 788).pointIds 788)]
theorem treeEq2309 : B2309.tree = HexagonCover.NBand.M7300_7500.SplitData.node2309 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2310
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2308 : Block := .branch 165 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 182698855038962130087031371948671701637744656400, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 519).pointIds 519), B2309, (.leaf 0 [] 0)]
theorem treeEq2308 : B2308.tree = HexagonCover.NBand.M7300_7500.SplitData.node2308 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2309
  · rfl

def B2307 : Block := .branch 167 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 182698855038962130087031371948671701637744656400, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 517).pointIds 517), B2308, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2307 : B2307.tree = HexagonCover.NBand.M7300_7500.SplitData.node2307 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2308
  · rfl

def B2306 : Block := .branch 143 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), B2307, (.leaf 5 (Common.fact 511).pointIds 511), (.leaf 6 (Common.fact 786).pointIds 786)]
theorem treeEq2306 : B2306.tree = HexagonCover.NBand.M7300_7500.SplitData.node2306 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2307
  · rfl
  · rfl

def B2305 : Block := .branch 129 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 494).pointIds 494), (.leaf 5 (Common.fact 301).pointIds 301), B2306]
theorem treeEq2305 : B2305.tree = HexagonCover.NBand.M7300_7500.SplitData.node2305 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2306

def B2304 : Block := .branch 130 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 488).pointIds 488), (.leaf 1 (Common.fact 489).pointIds 489), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 492).pointIds 492), (.leaf 5 (Common.fact 493).pointIds 493), B2305]
theorem treeEq2304 : B2304.tree = HexagonCover.NBand.M7300_7500.SplitData.node2304 := by
  change Tree.branch (130 : Fin 172) _ = Tree.branch (130 : Fin 172) _
  apply congrArg (Tree.branch (130 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2305

def B2303 : Block := .branch 131 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 482).pointIds 482), (.leaf 1 (Common.fact 483).pointIds 483), (.leaf 2 (Common.fact 484).pointIds 484), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 486).pointIds 486), (.leaf 5 (Common.fact 487).pointIds 487), B2304]
theorem treeEq2303 : B2303.tree = HexagonCover.NBand.M7300_7500.SplitData.node2303 := by
  change Tree.branch (131 : Fin 172) _ = Tree.branch (131 : Fin 172) _
  apply congrArg (Tree.branch (131 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2304

def B2302 : Block := .branch 163 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 248).pointIds 248), B2303]
theorem treeEq2302 : B2302.tree = HexagonCover.NBand.M7300_7500.SplitData.node2302 := by
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
  · exact treeEq2303

def B2301 : Block := .branch 151 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B2302, (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq2301 : B2301.tree = HexagonCover.NBand.M7300_7500.SplitData.node2301 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2302
  · rfl
  · rfl

def B2300 : Block := .branch 132 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 196).pointIds 196), (.leaf 5 (Common.fact 197).pointIds 197), B2301]
theorem treeEq2300 : B2300.tree = HexagonCover.NBand.M7300_7500.SplitData.node2300 := by
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
  · exact treeEq2301

def B2299 : Block := .branch 133 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 180).pointIds 180), (.leaf 1 (Common.fact 181).pointIds 181), (.leaf 2 (Common.fact 182).pointIds 182), (.leaf 3 (Common.fact 183).pointIds 183), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), B2300]
theorem treeEq2299 : B2299.tree = HexagonCover.NBand.M7300_7500.SplitData.node2299 := by
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
  · exact treeEq2300

def B2298 : Block := .branch 157 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B2299, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq2298 : B2298.tree = HexagonCover.NBand.M7300_7500.SplitData.node2298 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2299
  · rfl
  · rfl

theorem accepted2298 : B2298.accepted = true := by decide +kernel
theorem checked2298 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2298 (maskNeeds ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424]) := by
  rw [← treeEq2298]
  exact B2298.sound accepted2298
#print axioms checked2298

def Tip0073_1238 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1238 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0031.checked1238
def Tip0073_1765 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1765 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked1765
def Tip0073_0081 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0081 ![385, 147934241659377681922, 2416559502452970231812, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked0081
def Tip0073_2298 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2298 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] checked2298
def B0076 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 374144419178489218543400600972091306603544552407104] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M7300_7500.SplitData.node0076 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0075 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 374144419178489218543400600972091306603544552407104] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0076, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 375).pointIds 375)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M7300_7500.SplitData.node0075 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
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
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M7300_7500.SplitData.node0074 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0075

def B1237 : Block := .branch 72 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip0073_1238, Tip0073_1765, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M7300_7500.SplitData.node1237 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 71 ![385, 147934241659377681922, 55376261018147624964, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip0073_0081, B1237, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M7300_7500.SplitData.node0080 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1237
  · rfl
  · rfl
  · rfl

def B2295 : Block := .branch 132 ![385, 1538, 6148, 24584, 183401328512715844715989747074260125025183039504, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 196).pointIds 196), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq2295 : B2295.tree = HexagonCover.NBand.M7300_7500.SplitData.node2295 := by
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

def B2294 : Block := .branch 157 ![385, 1538, 6148, 24584, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B2295, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq2294 : B2294.tree = HexagonCover.NBand.M7300_7500.SplitData.node2294 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2295
  · rfl
  · rfl

def B2293 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 1538, 6148, 24584, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2294, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2293 : B2293.tree = HexagonCover.NBand.M7300_7500.SplitData.node2293 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2294
  · rfl

def B2292 : Block := .branch 168 ![385, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539375338196749860208704] ![B2293, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq2292 : B2292.tree = HexagonCover.NBand.M7300_7500.SplitData.node2292 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2293
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0079 : Block := .branch 67 ![385, 360289069701268994, 55376261018147624964, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 198).pointIds 198), B0080, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B2292]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M7300_7500.SplitData.node0079 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0080
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2292

def B0078 : Block := .branch 87 ![385, 360289069701268994, 55376261018147624964, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), (.leaf 4 (Common.fact 126).pointIds 126), (.leaf 5 (Common.fact 127).pointIds 127), B0079]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M7300_7500.SplitData.node0078 := by
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
  · exact treeEq0079

def B2297 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 1099511629314, 6148, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796759747059773240508480] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), Tip0073_2298, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2297 : B2297.tree = HexagonCover.NBand.M7300_7500.SplitData.node2297 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2296 : Block := .branch 168 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796759747059773240508480] ![B2297, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 784).pointIds 784)]
theorem treeEq2296 : B2296.tree = HexagonCover.NBand.M7300_7500.SplitData.node2296 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2297
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0077 : Block := .branch 65 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B0078, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B2296]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M7300_7500.SplitData.node0077 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0078
  · rfl
  · rfl
  · rfl
  · exact treeEq2296

def B0073 : Block := .branch 59 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![B0074, B0077, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M7300_7500.SplitData.node0073 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0074
  · exact treeEq0077
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0073 : B0073.accepted = true := by decide +kernel
theorem checked0073 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0073 (maskNeeds ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936]) := by
  rw [← treeEq0073]
  exact B0073.sound accepted0073
#print axioms checked0073

end HexagonCover.NBand.M7300_7500.SplitTree.Run0032
