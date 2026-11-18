import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0126_0137 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0137 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 40195491365410131941380, 79286190953605839793929871368, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] HexagonCover.NBand.M7500_7700.SplitTree.Run0001.checked0137
def B0237 : Block := .branch 171 ![748288838313422294120286634955199815871152049357185, 453347182355485940516354, 2923003274661805836407369743351613006661011118084, 174224571863520493331026730868022485999624, 17720707352637197883219678596684931613328182181904, 1496577676626844588240573268701473812127674924400672, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 645).pointIds 645), (.leaf 2 (Common.fact 511).pointIds 511), (.leaf 3 (Common.fact 646).pointIds 646), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M7500_7700.SplitData.node0237 := by
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

def B0236 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 453347182355485940516354, 2923003274661805836407369743351613006661011118084, 174224571863520493331026730868022485999624, 17720707352637197883219678596684931613328182181904, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 643).pointIds 643), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 644).pointIds 644), (.leaf 4 (Common.fact 528).pointIds 528), B0237, (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M7500_7700.SplitData.node0236 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0237
  · rfl

def B0235 : Block := .branch 137 ![748288838313422294120286634955199815871152049357185, 453347182355485940516354, 2923003274661805836407369743351613006661011118084, 37778931862957161734152, 17720707352637197883219678596684931613328182181904, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 286).pointIds 286), (.leaf 1 (Common.fact 287).pointIds 287), (.leaf 2 (Common.fact 288).pointIds 288), B0236, (.leaf 4 (Common.fact 642).pointIds 642), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M7500_7700.SplitData.node0235 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl
  · rfl
  · rfl

def B0234 : Block := .branch 76 ![748288838313422294120286634955199815871152049357185, 453347254413079978444290, 2923003274661805836407369667793749280746687698948, 37778931862957161734152, 17720707352637197883219678596684931613328182181904, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), B0235, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M7500_7700.SplitData.node0234 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0235
  · rfl
  · rfl
  · rfl
  · rfl

def B0233 : Block := .branch 77 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2923003274661805836407369667830642768894106802180, 37778931862957161734152, 17720707352637197883219678596684931613328182181904, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 352).pointIds 352), B0234, (.leaf 2 (Common.fact 639).pointIds 639), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M7500_7700.SplitData.node0233 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0234
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0232 : Block := .branch 161 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2398076729582241716228, 37778931862957161734152, 17720707352637197883219678596684931613328182181904, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), B0233, (.leaf 3 (Common.fact 638).pointIds 638), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M7500_7700.SplitData.node0232 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0233
  · rfl
  · rfl
  · rfl
  · rfl

def B0231 : Block := .branch 163 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2398076729582241716228, 37778931862957161734152, 6028694253989974537590199934954667456080721838096, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B0232, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 482).pointIds 482)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M7500_7700.SplitData.node0231 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0232
  · rfl
  · rfl

def B0230 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2398076729582241716228, 37778931862957161734152, 6028694253989974537590199934954667456080721838096, 42535295865117307932921825928971419680, 21799339131189997193194225157124669308992] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 277).pointIds 277), B0231]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M7500_7700.SplitData.node0230 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231

def B0229 : Block := .branch 162 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2398076729582241716228, 37778931862957161734152, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 636).pointIds 636), B0230, (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M7500_7700.SplitData.node0229 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl

def B0136 : Block := .branch 75 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2416559502452970231812, 79286190953605839793929871368, 182690840708656408144339882549917468632828444688, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), Tip0126_0137, B0229, (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 468).pointIds 468)]
theorem treeEq0136 : B0136.tree = HexagonCover.NBand.M7500_7700.SplitData.node0136 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0229
  · rfl
  · rfl
  · rfl

def B0135 : Block := .branch 138 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2416559502452970231812, 79286190953605839793929871368, 182690492259512681103353296054319458502179913744, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0136, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0135 : B0135.tree = HexagonCover.NBand.M7500_7700.SplitData.node0135 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0136
  · rfl
  · rfl

def B0134 : Block := .branch 141 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2416559502452970231812, 79286190953605839793929871368, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), B0135, (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0134 : B0134.tree = HexagonCover.NBand.M7500_7700.SplitData.node0134 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0135
  · rfl
  · rfl

def B0133 : Block := .branch 124 ![748288838313422294120286634955199815871152049357185, 302231526961251331606018, 2416559502452970231812, 79286190953605839793929871368, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 465).pointIds 465), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0134]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M7500_7700.SplitData.node0133 := by
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
  · exact treeEq0134

def B0132 : Block := .branch 79 ![748288838313422294120286634350736906063837462004097, 302231671076439407461890, 2416559502452970231812, 79286190953605839793929871368, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0133, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M7500_7700.SplitData.node0132 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0131 : Block := .branch 169 ![385, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0132, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M7500_7700.SplitData.node0131 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0132
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0130 : Block := .branch 132 ![385, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0131]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M7500_7700.SplitData.node0130 := by
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
  · exact treeEq0131

def B0129 : Block := .branch 133 ![385, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0130]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M7500_7700.SplitData.node0129 := by
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
  · exact treeEq0130

def B0128 : Block := .branch 157 ![385, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0129, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M7500_7700.SplitData.node0128 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0129
  · rfl
  · rfl

def B0127 : Block := .branch 125 ![590295810358705652097, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0128, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M7500_7700.SplitData.node0127 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0128
  · rfl

def B0126 : Block := .branch 149 ![590295810358705652097, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0127, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M7500_7700.SplitData.node0126 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0127
  · rfl
  · rfl

theorem accepted0126 : B0126.accepted = true := by decide +kernel
theorem checked0126 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0126 (maskNeeds ![590295810358705652097, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 98320, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0126]
  exact B0126.sound accepted0126
#print axioms checked0126

def B0256 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 665).pointIds 665), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M7500_7700.SplitData.node0256 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0255 : Block := .branch 139 ![385, 1538, 6148, 79228181403730269072124829704, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0256]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M7500_7700.SplitData.node0255 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0256

def B0254 : Block := .branch 151 ![385, 1538, 6148, 79228181403730269072124829704, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0255, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M7500_7700.SplitData.node0254 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0255
  · rfl
  · rfl

def B0253 : Block := .branch 163 ![385, 1538, 6148, 79228181403730269072124829704, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0254]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M7500_7700.SplitData.node0253 := by
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
  · exact treeEq0254

def B0252 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 11842809695321532143620, 79228181403730269072124829704, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), B0253, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M7500_7700.SplitData.node0252 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0253
  · rfl
  · rfl

def B0251 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 11842809695321532143620, 79228181403730269072124829704, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 653).pointIds 653), (.leaf 3 (Common.fact 654).pointIds 654), (.leaf 4 (Common.fact 655).pointIds 655), B0252, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M7500_7700.SplitData.node0251 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0252
  · rfl

def B0250 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 11842809695321532143620, 79228181403730269072124829704, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0251, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M7500_7700.SplitData.node0250 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0251
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0249 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79266867029957937205715427336, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0250, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M7500_7700.SplitData.node0249 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0250
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0248 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79266867029957937205715427336, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0249]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M7500_7700.SplitData.node0248 := by
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
  · exact treeEq0249

def B0247 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79266867029957937205715427336, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0248]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M7500_7700.SplitData.node0247 := by
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
  · exact treeEq0248

def B0246 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0247, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M7500_7700.SplitData.node0246 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · rfl
  · rfl

def B0245 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0246, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M7500_7700.SplitData.node0245 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0246
  · rfl

def B0244 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79266867029957937205715427336, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0245, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M7500_7700.SplitData.node0244 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl
  · rfl

def B0243 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 11861292468192260659204, 79266867029957937205715427336, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0244]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M7500_7700.SplitData.node0243 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0244

def B0260 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M7500_7700.SplitData.node0260 := by
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

def B0259 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0260, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M7500_7700.SplitData.node0259 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0260
  · rfl
  · rfl

def B0258 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0259, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M7500_7700.SplitData.node0258 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0259
  · rfl

def B0257 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0258, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M7500_7700.SplitData.node0257 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258
  · rfl
  · rfl

def B0242 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79286209843071771272510726152, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0243, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0257]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M7500_7700.SplitData.node0242 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0243
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0257

theorem accepted0242 : B0242.accepted = true := by decide +kernel
theorem checked0242 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0242 (maskNeeds ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79286209843071771272510726152, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0242]
  exact B0242.sound accepted0242
#print axioms checked0242

def B0276 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M7500_7700.SplitData.node0276 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0275 : Block := .branch 139 ![385, 1538, 6148, 79266857585224971466424999944, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0276]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M7500_7700.SplitData.node0275 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276

def B0274 : Block := .branch 151 ![385, 1538, 6148, 79266857585224971466424999944, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0275, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M7500_7700.SplitData.node0274 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0275
  · rfl
  · rfl

def B0273 : Block := .branch 163 ![385, 1538, 6148, 79266857585224971466424999944, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0274]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M7500_7700.SplitData.node0273 := by
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
  · exact treeEq0274

def B0272 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 7120443212451886929924, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 670).pointIds 670), (.leaf 3 (Common.fact 671).pointIds 671), B0273, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M7500_7700.SplitData.node0272 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0273
  · rfl
  · rfl

def B0271 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 7120443212451886929924, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 668).pointIds 668), (.leaf 3 (Common.fact 669).pointIds 669), (.leaf 4 (Common.fact 655).pointIds 655), B0272, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M7500_7700.SplitData.node0271 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0272
  · rfl

def B0270 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 7120443212451886929924, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0271, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M7500_7700.SplitData.node0270 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0271
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0269 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0270, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M7500_7700.SplitData.node0269 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0270
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0268 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0269]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M7500_7700.SplitData.node0268 := by
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
  · exact treeEq0269

def B0267 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0268]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M7500_7700.SplitData.node0267 := by
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
  · exact treeEq0268

def B0266 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0267, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M7500_7700.SplitData.node0266 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0267
  · rfl
  · rfl

def B0265 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0266, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M7500_7700.SplitData.node0265 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0266
  · rfl

def B0264 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0265, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M7500_7700.SplitData.node0264 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0265
  · rfl
  · rfl

def B0263 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 7138925985322615445508, 79266857585224971466424999944, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0264]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M7500_7700.SplitData.node0263 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0264

def B0280 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M7500_7700.SplitData.node0280 := by
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

def B0279 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0280, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M7500_7700.SplitData.node0279 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280
  · rfl
  · rfl

def B0278 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0279, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M7500_7700.SplitData.node0278 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0279
  · rfl

def B0277 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0278, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M7500_7700.SplitData.node0277 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0278
  · rfl
  · rfl

def B0262 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0263, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0277]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M7500_7700.SplitData.node0262 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0263
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0277

theorem accepted0262 : B0262.accepted = true := by decide +kernel
theorem checked0262 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0262 (maskNeeds ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0262]
  exact B0262.sound accepted0262
#print axioms checked0262

def Tip0261_0262 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0262 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] checked0262
def B0295 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 672).pointIds 672), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M7500_7700.SplitData.node0295 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0294 : Block := .branch 139 ![385, 1538, 6148, 79266857585224971466424999944, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0295]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M7500_7700.SplitData.node0294 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0295

def B0293 : Block := .branch 151 ![385, 1538, 6148, 79266857585224971466424999944, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0294, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M7500_7700.SplitData.node0293 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0294
  · rfl
  · rfl

def B0292 : Block := .branch 163 ![385, 1538, 6148, 79266857585224971466424999944, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0293]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M7500_7700.SplitData.node0292 := by
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
  · exact treeEq0293

def B0291 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 7120443212451886929924, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 670).pointIds 670), (.leaf 3 (Common.fact 671).pointIds 671), B0292, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M7500_7700.SplitData.node0291 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0292
  · rfl
  · rfl

def B0290 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 7120443212451886929924, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 668).pointIds 668), (.leaf 3 (Common.fact 669).pointIds 669), (.leaf 4 (Common.fact 655).pointIds 655), B0291, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M7500_7700.SplitData.node0290 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0291
  · rfl

def B0289 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 7120443212451886929924, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0290, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M7500_7700.SplitData.node0289 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0290
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0288 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0289, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M7500_7700.SplitData.node0288 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0287 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0288]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M7500_7700.SplitData.node0287 := by
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
  · exact treeEq0288

def B0286 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0287]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M7500_7700.SplitData.node0286 := by
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
  · exact treeEq0287

def B0285 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0286, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M7500_7700.SplitData.node0285 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl
  · rfl

def B0284 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0285, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M7500_7700.SplitData.node0284 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0285
  · rfl

def B0283 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79266857585224971466424999944, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0284, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M7500_7700.SplitData.node0283 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0284
  · rfl
  · rfl

def B0282 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 7138925985322615445508, 79266857585224971466424999944, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0283]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M7500_7700.SplitData.node0282 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283

def B0299 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M7500_7700.SplitData.node0299 := by
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

def B0298 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0299, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M7500_7700.SplitData.node0298 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0299
  · rfl
  · rfl

def B0297 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0298, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M7500_7700.SplitData.node0297 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0298
  · rfl

def B0296 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0297, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M7500_7700.SplitData.node0296 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0297
  · rfl
  · rfl

def B0281 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0282, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0296]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M7500_7700.SplitData.node0281 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0282
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0296

def B0261 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0261_0262, B0281, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M7500_7700.SplitData.node0261 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0281
  · rfl
  · rfl
  · rfl

theorem accepted0261 : B0261.accepted = true := by decide +kernel
theorem checked0261 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0261 (maskNeeds ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0261]
  exact B0261.sound accepted0261
#print axioms checked0261

end HexagonCover.NBand.M7500_7700.SplitTree.Run0002
