import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0029
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0030
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2164_2166 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2166 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0029.checked2166
def B2203 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq2203 : B2203.tree = HexagonCover.NBand.M7300_7500.SplitData.node2203 := by
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

def B2202 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2203, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq2202 : B2202.tree = HexagonCover.NBand.M7300_7500.SplitData.node2202 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2203
  · rfl
  · rfl

def B2201 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2202]
theorem treeEq2201 : B2201.tree = HexagonCover.NBand.M7300_7500.SplitData.node2201 := by
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
  · exact treeEq2202

def B2200 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2201, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2200 : B2200.tree = HexagonCover.NBand.M7300_7500.SplitData.node2200 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2201
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2199 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2200]
theorem treeEq2199 : B2199.tree = HexagonCover.NBand.M7300_7500.SplitData.node2199 := by
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
  · exact treeEq2200

def B2198 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2199, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2198 : B2198.tree = HexagonCover.NBand.M7300_7500.SplitData.node2198 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2199
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2197 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2198, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2197 : B2197.tree = HexagonCover.NBand.M7300_7500.SplitData.node2197 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2198
  · rfl

def B2196 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2197, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq2196 : B2196.tree = HexagonCover.NBand.M7300_7500.SplitData.node2196 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2197
  · rfl
  · rfl

def B2165 : Block := .branch 89 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip2164_2166, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2196]
theorem treeEq2165 : B2165.tree = HexagonCover.NBand.M7300_7500.SplitData.node2165 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2196

def B2211 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq2211 : B2211.tree = HexagonCover.NBand.M7300_7500.SplitData.node2211 := by
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

def B2210 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2211, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq2210 : B2210.tree = HexagonCover.NBand.M7300_7500.SplitData.node2210 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2211
  · rfl
  · rfl

def B2209 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2210]
theorem treeEq2209 : B2209.tree = HexagonCover.NBand.M7300_7500.SplitData.node2209 := by
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
  · exact treeEq2210

def B2208 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B2209, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2208 : B2208.tree = HexagonCover.NBand.M7300_7500.SplitData.node2208 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2209
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2207 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2208]
theorem treeEq2207 : B2207.tree = HexagonCover.NBand.M7300_7500.SplitData.node2207 := by
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
  · exact treeEq2208

def B2206 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B2207, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2206 : B2206.tree = HexagonCover.NBand.M7300_7500.SplitData.node2206 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2207
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2205 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2206, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2205 : B2205.tree = HexagonCover.NBand.M7300_7500.SplitData.node2205 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2206
  · rfl

def B2204 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2205, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq2204 : B2204.tree = HexagonCover.NBand.M7300_7500.SplitData.node2204 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2205
  · rfl
  · rfl

def B2164 : Block := .branch 86 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B2165, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B2204]
theorem treeEq2164 : B2164.tree = HexagonCover.NBand.M7300_7500.SplitData.node2164 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2165
  · rfl
  · rfl
  · exact treeEq2204

theorem accepted2164 : B2164.accepted = true := by decide +kernel
theorem checked2164 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2164 (maskNeeds ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2164]
  exact B2164.sound accepted2164
#print axioms checked2164

def B2245 : Block := .branch 142 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 24114777037737969633617774127089565776794307002432] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq2245 : B2245.tree = HexagonCover.NBand.M7300_7500.SplitData.node2245 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2244 : Block := .branch 159 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2245]
theorem treeEq2244 : B2244.tree = HexagonCover.NBand.M7300_7500.SplitData.node2244 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2245

def B2243 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2244]
theorem treeEq2243 : B2243.tree = HexagonCover.NBand.M7300_7500.SplitData.node2243 := by
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
  · exact treeEq2244

def B2242 : Block := .branch 169 ![2535301200456458802993406411137, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B2243, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2242 : B2242.tree = HexagonCover.NBand.M7300_7500.SplitData.node2242 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2243
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2241 : Block := .branch 170 ![2535301200456458802993406411137, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 679).pointIds 679), B2242, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2241 : B2241.tree = HexagonCover.NBand.M7300_7500.SplitData.node2241 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2242
  · rfl

def B2250 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq2250 : B2250.tree = HexagonCover.NBand.M7300_7500.SplitData.node2250 := by
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

def B2249 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2250]
theorem treeEq2249 : B2249.tree = HexagonCover.NBand.M7300_7500.SplitData.node2249 := by
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
  · exact treeEq2250

def B2248 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 42535295865117307932921825928971419680, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), B2249, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2248 : B2248.tree = HexagonCover.NBand.M7300_7500.SplitData.node2248 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2249
  · rfl
  · rfl

def B2247 : Block := .branch 125 ![374144419156711157447272335445480168895904795853185, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 393248, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2248, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2247 : B2247.tree = HexagonCover.NBand.M7300_7500.SplitData.node2247 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2248
  · rfl

def B2246 : Block := .branch 168 ![10387129018270111715863986064851329, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071807775992273212354753230527791168] ![B2247, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq2246 : B2246.tree = HexagonCover.NBand.M7300_7500.SplitData.node2246 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2240 : Block := .branch 108 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B2241, (.leaf 5 (Common.fact 308).pointIds 308), B2246]
theorem treeEq2240 : B2240.tree = HexagonCover.NBand.M7300_7500.SplitData.node2240 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2241
  · rfl
  · exact treeEq2246

theorem accepted2240 : B2240.accepted = true := by decide +kernel
theorem checked2240 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2240 (maskNeeds ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2240]
  exact B2240.sound accepted2240
#print axioms checked2240

def Tip2238_2240 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2240 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2240
def B2259 : Block := .branch 109 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq2259 : B2259.tree = HexagonCover.NBand.M7300_7500.SplitData.node2259 := by
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

def B2258 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B2259, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq2258 : B2258.tree = HexagonCover.NBand.M7300_7500.SplitData.node2258 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2259
  · rfl
  · rfl

def B2257 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B2258, (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq2257 : B2257.tree = HexagonCover.NBand.M7300_7500.SplitData.node2257 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2258
  · rfl

def B2256 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2257]
theorem treeEq2256 : B2256.tree = HexagonCover.NBand.M7300_7500.SplitData.node2256 := by
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
  · exact treeEq2257

def B2255 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B2256, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2255 : B2255.tree = HexagonCover.NBand.M7300_7500.SplitData.node2255 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2256
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2254 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2255]
theorem treeEq2254 : B2254.tree = HexagonCover.NBand.M7300_7500.SplitData.node2254 := by
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
  · exact treeEq2255

def B2253 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739815242086773067913625664] ![B2254, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2253 : B2253.tree = HexagonCover.NBand.M7300_7500.SplitData.node2253 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2254
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2252 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2253, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2252 : B2252.tree = HexagonCover.NBand.M7300_7500.SplitData.node2252 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2253
  · rfl

def B2251 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2252, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq2251 : B2251.tree = HexagonCover.NBand.M7300_7500.SplitData.node2251 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2252
  · rfl
  · rfl

def B2239 : Block := .branch 101 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip2238_2240, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B2251]
theorem treeEq2239 : B2239.tree = HexagonCover.NBand.M7300_7500.SplitData.node2239 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2251

def B2267 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq2267 : B2267.tree = HexagonCover.NBand.M7300_7500.SplitData.node2267 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2266 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2267, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq2266 : B2266.tree = HexagonCover.NBand.M7300_7500.SplitData.node2266 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2267
  · rfl
  · rfl

def B2265 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2266]
theorem treeEq2265 : B2265.tree = HexagonCover.NBand.M7300_7500.SplitData.node2265 := by
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
  · exact treeEq2266

def B2264 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B2265, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2264 : B2264.tree = HexagonCover.NBand.M7300_7500.SplitData.node2264 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2265
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2263 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2264]
theorem treeEq2263 : B2263.tree = HexagonCover.NBand.M7300_7500.SplitData.node2263 := by
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
  · exact treeEq2264

def B2262 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B2263, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2262 : B2262.tree = HexagonCover.NBand.M7300_7500.SplitData.node2262 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2263
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2261 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2262, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2261 : B2261.tree = HexagonCover.NBand.M7300_7500.SplitData.node2261 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2262
  · rfl

def B2260 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2261, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq2260 : B2260.tree = HexagonCover.NBand.M7300_7500.SplitData.node2260 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2261
  · rfl
  · rfl

def B2238 : Block := .branch 89 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 86).pointIds 86), B2239, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2260]
theorem treeEq2238 : B2238.tree = HexagonCover.NBand.M7300_7500.SplitData.node2238 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2239
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2260

theorem accepted2238 : B2238.accepted = true := by decide +kernel
theorem checked2238 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2238 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2238]
  exact B2238.sound accepted2238
#print axioms checked2238

def Tip2236_2238 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2238 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2238
def B2274 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq2274 : B2274.tree = HexagonCover.NBand.M7300_7500.SplitData.node2274 := by
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

def B2273 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2274, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq2273 : B2273.tree = HexagonCover.NBand.M7300_7500.SplitData.node2273 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2274
  · rfl
  · rfl

def B2272 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 23384026219072518174516009081983879603233521926208] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2273]
theorem treeEq2272 : B2272.tree = HexagonCover.NBand.M7300_7500.SplitData.node2272 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2273

def B2271 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2272]
theorem treeEq2271 : B2271.tree = HexagonCover.NBand.M7300_7500.SplitData.node2271 := by
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
  · exact treeEq2272

def B2270 : Block := .branch 169 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515986038083306341688410176] ![B2271, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2270 : B2270.tree = HexagonCover.NBand.M7300_7500.SplitData.node2270 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2271
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2269 : Block := .branch 170 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2270, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2269 : B2269.tree = HexagonCover.NBand.M7300_7500.SplitData.node2269 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2270
  · rfl

def B2268 : Block := .branch 171 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2269, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq2268 : B2268.tree = HexagonCover.NBand.M7300_7500.SplitData.node2268 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2269
  · rfl
  · rfl

def B2237 : Block := .branch 86 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), Tip2236_2238, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B2268]
theorem treeEq2237 : B2237.tree = HexagonCover.NBand.M7300_7500.SplitData.node2237 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2268

def B2282 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 721).pointIds 721)]
theorem treeEq2282 : B2282.tree = HexagonCover.NBand.M7300_7500.SplitData.node2282 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2281 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2282, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq2281 : B2281.tree = HexagonCover.NBand.M7300_7500.SplitData.node2281 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2282
  · rfl
  · rfl

def B2280 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515932012962879170623634407488] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2281]
theorem treeEq2280 : B2280.tree = HexagonCover.NBand.M7300_7500.SplitData.node2280 := by
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
  · exact treeEq2281

def B2279 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241497972700515692359188544] ![B2280, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2279 : B2279.tree = HexagonCover.NBand.M7300_7500.SplitData.node2279 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2280
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2278 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2279]
theorem treeEq2278 : B2278.tree = HexagonCover.NBand.M7300_7500.SplitData.node2278 := by
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
  · exact treeEq2279

def B2277 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438917017082873731800891456] ![B2278, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2277 : B2277.tree = HexagonCover.NBand.M7300_7500.SplitData.node2277 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2278
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2276 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B2277, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2276 : B2276.tree = HexagonCover.NBand.M7300_7500.SplitData.node2276 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2277
  · rfl

def B2275 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B2276, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq2275 : B2275.tree = HexagonCover.NBand.M7300_7500.SplitData.node2275 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2276
  · rfl
  · rfl

def B2236 : Block := .branch 78 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 134).pointIds 134), B2237, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B2275]
theorem treeEq2236 : B2236.tree = HexagonCover.NBand.M7300_7500.SplitData.node2236 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2237
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2275

theorem accepted2236 : B2236.accepted = true := by decide +kernel
theorem checked2236 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2236 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2236]
  exact B2236.sound accepted2236
#print axioms checked2236

end HexagonCover.NBand.M7300_7500.SplitTree.Run0030
