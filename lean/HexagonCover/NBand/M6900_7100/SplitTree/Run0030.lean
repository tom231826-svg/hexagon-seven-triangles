import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0028
import HexagonCover.NBand.M6900_7100.SplitTree.Run0029
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0030
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2138_2149 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2149 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 2923003274661805836407369745712796248095833724932, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] HexagonCover.NBand.M6900_7100.SplitTree.Run0028.checked2149
def Tip2138_2190 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2190 ![2535301200456458802993406411137, 618970168153392549130667522, 89780339435541406685188, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] HexagonCover.NBand.M6900_7100.SplitTree.Run0029.checked2190
def Tip2138_2202 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2202 ![385, 618970168153392549130667522, 80335606469802116257796, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] HexagonCover.NBand.M6900_7100.SplitTree.Run0029.checked2202
def Tip2138_2216 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2216 ![385, 618970168153392549130667522, 80335606469802116257796, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] HexagonCover.NBand.M6900_7100.SplitTree.Run0029.checked2216
def Tip2138_2232 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2232 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79344221754130583429138374664, 1496578390250690941220513797844458536875243115479056, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] HexagonCover.NBand.M6900_7100.SplitTree.Run0029.checked2232
def B2189 : Block := .branch 124 ![730750818665451459101842416358141509827966271873, 1538, 6148, 24584, 98320, 393248, 374144435904048117441368111866384921762350044282944] ![(.leaf 0 (Common.fact 827).pointIds 827), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq2189 : B2189.tree = HexagonCover.NBand.M6900_7100.SplitData.node2189 := by
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

def B2188 : Block := .branch 159 ![385, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144435904048117441368111866384921762350044282944] ![B2189, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq2188 : B2188.tree = HexagonCover.NBand.M6900_7100.SplitData.node2188 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2189
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2187 : Block := .branch 168 ![385, 618970610298789565856482818, 4384504911992708754611054502871215541837442848772, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2188]
theorem treeEq2187 : B2187.tree = HexagonCover.NBand.M6900_7100.SplitData.node2187 := by
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
  · exact treeEq2188

def B2186 : Block := .branch 160 ![385, 618970610298789565856482818, 2923003274661805836407369670154932522181510305796, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 600).pointIds 600), B2187, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 778).pointIds 778)]
theorem treeEq2186 : B2186.tree = HexagonCover.NBand.M6900_7100.SplitData.node2186 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2187
  · rfl
  · rfl
  · rfl
  · rfl

def B2148 : Block := .branch 69 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 2923003274661805836407369745712796248095833724932, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![Tip2138_2149, B2186, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 773).pointIds 773)]
theorem treeEq2148 : B2148.tree = HexagonCover.NBand.M6900_7100.SplitData.node2148 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2186
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2147 : Block := .branch 161 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B2148, (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 772).pointIds 772)]
theorem treeEq2147 : B2147.tree = HexagonCover.NBand.M6900_7100.SplitData.node2147 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2148
  · rfl
  · rfl
  · rfl
  · rfl

def B2146 : Block := .branch 143 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 498).pointIds 498), B2147]
theorem treeEq2146 : B2146.tree = HexagonCover.NBand.M6900_7100.SplitData.node2146 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2147

def B2145 : Block := .branch 150 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 42535295865117307932921825928971419680, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2146, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2145 : B2145.tree = HexagonCover.NBand.M6900_7100.SplitData.node2145 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2146
  · rfl
  · rfl

def B2144 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 393248, 5596964371115913223923157332406250560290880] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2145, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2144 : B2144.tree = HexagonCover.NBand.M6900_7100.SplitData.node2144 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2145
  · rfl

def B2143 : Block := .branch 169 ![2535301200456458802993406411137, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 393248, 5596964371115913223923157332406250560290880] ![B2144, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2143 : B2143.tree = HexagonCover.NBand.M6900_7100.SplitData.node2143 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2144
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2142 : Block := .branch 142 ![2535301200456458802993406411137, 618970020579439959454254594, 80298712981654697154564, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B2143]
theorem treeEq2142 : B2142.tree = HexagonCover.NBand.M6900_7100.SplitData.node2142 := by
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
  · exact treeEq2143

def B2141 : Block := .branch 108 ![2535301200456458802993406411137, 618970168153392549130667522, 89780339435541406685188, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2142, (.leaf 5 (Common.fact 322).pointIds 322), Tip2138_2190]
theorem treeEq2141 : B2141.tree = HexagonCover.NBand.M6900_7100.SplitData.node2141 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2142
  · rfl
  · rfl

def B2140 : Block := .branch 101 ![385, 618970168153392549130667522, 89780339435541406685188, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B2141, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), Tip2138_2202]
theorem treeEq2140 : B2140.tree = HexagonCover.NBand.M6900_7100.SplitData.node2140 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2141
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2139 : Block := .branch 91 ![385, 618970168153392549130667522, 89780339435541406685188, 116059239866245835594424328, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B2140, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), Tip2138_2216]
theorem treeEq2139 : B2139.tree = HexagonCover.NBand.M6900_7100.SplitData.node2139 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2140
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2231 : Block := .branch 144 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79344221754130583429138374664, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), (.leaf 4 (Common.fact 114).pointIds 114), Tip2138_2232, (.leaf 6 (Common.fact 115).pointIds 115)]
theorem treeEq2231 : B2231.tree = HexagonCover.NBand.M6900_7100.SplitData.node2231 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2230 : Block := .branch 170 ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79344221754130583429138374664, 713623846352979940529142984724747568191471632, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2231, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 869).pointIds 869)]
theorem treeEq2230 : B2230.tree = HexagonCover.NBand.M6900_7100.SplitData.node2230 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2231
  · rfl
  · rfl

def B2138 : Block := .branch 89 ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79344221754130583429138374664, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 104).pointIds 104), B2139, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2230]
theorem treeEq2138 : B2138.tree = HexagonCover.NBand.M6900_7100.SplitData.node2138 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2139
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2230

theorem accepted2138 : B2138.accepted = true := by decide +kernel
theorem checked2138 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2138 (maskNeeds ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79344221754130583429138374664, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2138]
  exact B2138.sound accepted2138
#print axioms checked2138

def Tip2137_2259 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2259 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] HexagonCover.NBand.M6900_7100.SplitTree.Run0029.checked2259
def Tip2137_2138 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2138 ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79344221754130583429138374664, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2138
def B2279 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293113493882659420268109258760, 11692015886240373161957371353695048238292648689680, 393248, 21778071483257670652985130252961727381568] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 917).pointIds 917), (.leaf 4 (Common.fact 888).pointIds 888), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 924).pointIds 924)]
theorem treeEq2279 : B2279.tree = HexagonCover.NBand.M6900_7100.SplitData.node2279 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2278 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1508269692861534105129571626641664458376098221228048, 43556142965880123323311949751266331459616, 5596964371115913456036914698415052103876672] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 844).pointIds 844), B2279, (.leaf 4 (Common.fact 873).pointIds 873), (.leaf 5 (Common.fact 907).pointIds 907), (.leaf 6 (Common.fact 923).pointIds 923)]
theorem treeEq2278 : B2278.tree = HexagonCover.NBand.M6900_7100.SplitData.node2278 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2279
  · rfl
  · rfl
  · rfl

def B2277 : Block := .branch 142 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1508269692861534105129571626641664458376098221228048, 43556142965880123323311949751266331459616, 21778071483257670652985130252961727381568] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 886).pointIds 886), (.leaf 5 (Common.fact 156).pointIds 156), B2278]
theorem treeEq2277 : B2277.tree = HexagonCover.NBand.M6900_7100.SplitData.node2277 := by
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
  · exact treeEq2278

def B2276 : Block := .branch 163 ![1208925819614629174706561, 302231526962350843233794, 89724963174523259066372, 38687987410909568413229064, 1496577679762886881783942147979934194218850760884240, 43556142965880123323311949751266331459616, 21778071483257670652985130252961727381568] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2277, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 922).pointIds 922)]
theorem treeEq2276 : B2276.tree = HexagonCover.NBand.M6900_7100.SplitData.node2276 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2277
  · rfl
  · rfl

def B2258 : Block := .branch 89 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip2137_2259, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2276]
theorem treeEq2258 : B2258.tree = HexagonCover.NBand.M6900_7100.SplitData.node2258 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2276

def B2285 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 1122433257491911512663687003209070846658580470825024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 930).pointIds 930), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 931).pointIds 931)]
theorem treeEq2285 : B2285.tree = HexagonCover.NBand.M6900_7100.SplitData.node2285 := by
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

def B2284 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 1122433257491911512663687003209070846658580470825024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2285, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq2284 : B2284.tree = HexagonCover.NBand.M6900_7100.SplitData.node2284 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2285
  · rfl
  · rfl

def B2283 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 393248, 374144419178489218543400368858333940594743008821312] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2284]
theorem treeEq2283 : B2283.tree = HexagonCover.NBand.M6900_7100.SplitData.node2283 := by
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
  · exact treeEq2284

def B2282 : Block := .branch 171 ![385, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 2854538941554885642239895250848741539096952864, 374144419178489218543400678343343761939811733602368] ![B2283, (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 832).pointIds 832), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 881).pointIds 881), (.leaf 5 (Common.fact 927).pointIds 927), (.leaf 6 (Common.fact 913).pointIds 913)]
theorem treeEq2282 : B2282.tree = HexagonCover.NBand.M6900_7100.SplitData.node2282 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2283
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2281 : Block := .branch 151 ![385, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2282, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq2281 : B2281.tree = HexagonCover.NBand.M6900_7100.SplitData.node2281 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2282
  · rfl

def B2280 : Block := .branch 168 ![385, 302232391653479298369026, 89817232923688825788420, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), (.leaf 2 (Common.fact 925).pointIds 925), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2281]
theorem treeEq2280 : B2280.tree = HexagonCover.NBand.M6900_7100.SplitData.node2280 := by
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
  · exact treeEq2281

def B2257 : Block := .branch 66 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 902).pointIds 902), B2258, B2280, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 904).pointIds 904), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 906).pointIds 906)]
theorem treeEq2257 : B2257.tree = HexagonCover.NBand.M6900_7100.SplitData.node2257 := by
  change Tree.branch (66 : Fin 173) _ = Tree.branch (66 : Fin 173) _
  apply congrArg (Tree.branch (66 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2258
  · exact treeEq2280
  · rfl
  · rfl
  · rfl
  · rfl

def B2256 : Block := .branch 135 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 38687987410909568413229064, 1496578393386733234763882677122918918966418952257552, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 896).pointIds 896), (.leaf 1 (Common.fact 897).pointIds 897), (.leaf 2 (Common.fact 898).pointIds 898), (.leaf 3 (Common.fact 899).pointIds 899), (.leaf 4 (Common.fact 900).pointIds 900), B2257, (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq2256 : B2256.tree = HexagonCover.NBand.M6900_7100.SplitData.node2256 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2257
  · rfl

def B2255 : Block := .branch 138 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79266850501675247161957179400, 1496578393038284091036841690536423320956288303726608, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B2256, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 895).pointIds 895)]
theorem treeEq2255 : B2255.tree = HexagonCover.NBand.M6900_7100.SplitData.node2255 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2256
  · rfl
  · rfl

def B2254 : Block := .branch 141 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79266850501675247161957179400, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B2255, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 894).pointIds 894)]
theorem treeEq2254 : B2254.tree = HexagonCover.NBand.M6900_7100.SplitData.node2254 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2255
  · rfl
  · rfl

def B2253 : Block := .branch 144 ![1208925819614629174706561, 302232391653479298369026, 89743445947393987581956, 79266850501675247161957179400, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), (.leaf 4 (Common.fact 114).pointIds 114), B2254, (.leaf 6 (Common.fact 893).pointIds 893)]
theorem treeEq2253 : B2253.tree = HexagonCover.NBand.M6900_7100.SplitData.node2253 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2254
  · rfl

def B2252 : Block := .branch 170 ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), B2253, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 892).pointIds 892)]
theorem treeEq2252 : B2252.tree = HexagonCover.NBand.M6900_7100.SplitData.node2252 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2253
  · rfl
  · rfl

def B2137 : Block := .branch 86 ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip2137_2138, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B2252]
theorem treeEq2137 : B2137.tree = HexagonCover.NBand.M6900_7100.SplitData.node2137 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2252

theorem accepted2137 : B2137.accepted = true := by decide +kernel
theorem checked2137 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2137 (maskNeeds ![1208925819614629174706561, 302379965606068974781954, 89780339435541406685188, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2137]
  exact B2137.sound accepted2137
#print axioms checked2137

def B2320 : Block := .branch 142 ![385, 1538, 6148, 24584, 1427247692706284399611944396176278292403421200, 393248, 2993155353275467248613440619107071973774133309210688] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 957).pointIds 957), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq2320 : B2320.tree = HexagonCover.NBand.M6900_7100.SplitData.node2320 := by
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
  · rfl

def B2319 : Block := .branch 171 ![10384593717070245552871351364092289, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539059264340141087380901025860594794512, 2854495427947215627233879871820816201736912928, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 791).pointIds 791), B2320]
theorem treeEq2319 : B2319.tree = HexagonCover.NBand.M6900_7100.SplitData.node2319 := by
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
  · exact treeEq2320

def B2318 : Block := .branch 151 ![10384593717070245552871351364092289, 147646011283225970178, 33093458868234935605252, 38687987410909568413229064, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 662).pointIds 662), B2319, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2318 : B2318.tree = HexagonCover.NBand.M6900_7100.SplitData.node2318 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2319
  · rfl

def B2328 : Block := .branch 118 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 185542200051774784537577176028434367729757159440, 393248, 1496577676648622660048031884097114377512928188825664] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 847).pointIds 847), (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq2328 : B2328.tree = HexagonCover.NBand.M6900_7100.SplitData.node2328 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2327 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 186255823898127764478106319013159115297948532752, 393248, 1496577676648622660048031884097114377512928188825664] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), B2328, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq2327 : B2327.tree = HexagonCover.NBand.M6900_7100.SplitData.node2327 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2328
  · rfl
  · rfl
  · rfl

def B2326 : Block := .branch 170 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 186255823898127764478106319013159115297948532752, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 838).pointIds 838), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2327]
theorem treeEq2326 : B2326.tree = HexagonCover.NBand.M6900_7100.SplitData.node2326 := by
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
  · exact treeEq2327

def B2325 : Block := .branch 151 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 183401328512715844715989747074260125025183039504, 2993155353253731711777011654710880546081278819434528, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2326, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2325 : B2325.tree = HexagonCover.NBand.M6900_7100.SplitData.node2325 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2326
  · rfl
  · rfl

def B2324 : Block := .branch 132 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 184828576205421804597048033043709620161565786128, 2993155353253731711777011654710880546081278819434528, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B2325]
theorem treeEq2324 : B2324.tree = HexagonCover.NBand.M6900_7100.SplitData.node2324 := by
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
  · exact treeEq2325

def B2323 : Block := .branch 133 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 184828576205421804597048033043709620161565786128, 2993155353253731711777011654710880546081278819434528, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2324]
theorem treeEq2323 : B2323.tree = HexagonCover.NBand.M6900_7100.SplitData.node2323 := by
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
  · exact treeEq2324

def B2322 : Block := .branch 157 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 2993155353253731711777011654710880546081278819434528, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2323, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2322 : B2322.tree = HexagonCover.NBand.M6900_7100.SplitData.node2322 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2323
  · rfl
  · rfl

def B2321 : Block := .branch 171 ![10384596192950324123631901162340737, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), B2322, (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq2321 : B2321.tree = HexagonCover.NBand.M6900_7100.SplitData.node2321 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2322
  · rfl

def B2317 : Block := .branch 108 ![10384596192950324123631901162340737, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2318, (.leaf 5 (Common.fact 322).pointIds 322), B2321]
theorem treeEq2317 : B2317.tree = HexagonCover.NBand.M6900_7100.SplitData.node2317 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2318
  · rfl
  · exact treeEq2321

theorem accepted2317 : B2317.accepted = true := by decide +kernel
theorem checked2317 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2317 (maskNeeds ![10384596192950324123631901162340737, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840]) := by
  rw [← treeEq2317]
  exact B2317.sound accepted2317
#print axioms checked2317

def Tip2315_2317 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2317 ![10384596192950324123631901162340737, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] checked2317
def B2337 : Block := .branch 142 ![385, 1538, 6148, 24584, 184115126923923055097950646770158485090466889744, 393248, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 967).pointIds 967), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq2337 : B2337.tree = HexagonCover.NBand.M6900_7100.SplitData.node2337 := by
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
  · rfl

def B2336 : Block := .branch 128 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 184115126583640688177012183306783877658698678288, 393248, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), (.leaf 3 (Common.fact 965).pointIds 965), B2337, (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq2336 : B2336.tree = HexagonCover.NBand.M6900_7100.SplitData.node2336 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2337
  · rfl
  · rfl

def B2335 : Block := .branch 163 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 184115126583640688177012183306783877658698678288, 393248, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 964).pointIds 964), (.leaf 5 (Common.fact 262).pointIds 262), B2336]
theorem treeEq2335 : B2335.tree = HexagonCover.NBand.M6900_7100.SplitData.node2335 := by
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
  · exact treeEq2336

def B2334 : Block := .branch 137 ![385, 1538, 6148, 5986310706507378352962293152179508887088401699856392, 184114952359068824656518890058984872593374412816, 393248, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 806).pointIds 806), B2335, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2334 : B2334.tree = HexagonCover.NBand.M6900_7100.SplitData.node2334 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2335
  · rfl
  · rfl

def B2333 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 184828576205421804597048033043709620161565786128, 393248, 27222590003029716089557985927829202141248] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), B2334, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq2333 : B2333.tree = HexagonCover.NBand.M6900_7100.SplitData.node2333 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2334
  · rfl
  · rfl
  · rfl

def B2332 : Block := .branch 132 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 184828576205421804597048033043709620161565786128, 393248, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B2333]
theorem treeEq2332 : B2332.tree = HexagonCover.NBand.M6900_7100.SplitData.node2332 := by
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
  · exact treeEq2333

def B2331 : Block := .branch 133 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 184828576205421804597048033043709620161565786128, 393248, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2332]
theorem treeEq2331 : B2331.tree = HexagonCover.NBand.M6900_7100.SplitData.node2331 := by
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
  · exact treeEq2332

def B2330 : Block := .branch 157 ![10384596192949733827821542456689025, 147646011283225970178, 33093458868234935605252, 77373613638577702003826696, 2140871539058939821587428954174242704574218256, 2993155353253731711777011654710880546081278819434528, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2331, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2330 : B2330.tree = HexagonCover.NBand.M6900_7100.SplitData.node2330 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2331
  · rfl
  · rfl

def B2329 : Block := .branch 171 ![10384596192950324123631901162340737, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), B2330, (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq2329 : B2329.tree = HexagonCover.NBand.M6900_7100.SplitData.node2329 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2330
  · rfl

def B2316 : Block := .branch 89 ![10384596192950324123631901162340737, 147646011283225970178, 33093458868234935605252, 116059239866245835594424328, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip2315_2317, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2329]
theorem treeEq2316 : B2316.tree = HexagonCover.NBand.M6900_7100.SplitData.node2316 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2329

def B2344 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq2344 : B2344.tree = HexagonCover.NBand.M6900_7100.SplitData.node2344 := by
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

def B2343 : Block := .branch 159 ![10384593717069655257060992658440577, 906694436769665430586882, 6148, 24584, 98320, 393248, 32667107873447277256147734942493049356352] ![B2344, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq2343 : B2343.tree = HexagonCover.NBand.M6900_7100.SplitData.node2343 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2344
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2342 : Block := .branch 77 ![10384593717069655257060992658440577, 906694436769665430586882, 1461501637330902918203684837438649502525577762820, 24584, 98320, 393248, 32667107873447277256147734942493049356352] ![(.leaf 0 (Common.fact 305).pointIds 305), B2343, (.leaf 2 (Common.fact 971).pointIds 971), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq2342 : B2342.tree = HexagonCover.NBand.M6900_7100.SplitData.node2342 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2343
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2341 : Block := .branch 160 ![10384593717069655257060992658440577, 906694436769665430586882, 4722366482869645219844, 24584, 98320, 393248, 32667107873447277256147734942493049356352] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B2342, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq2341 : B2341.tree = HexagonCover.NBand.M6900_7100.SplitData.node2341 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2342
  · rfl
  · rfl
  · rfl
  · rfl

def B2340 : Block := .branch 133 ![10384593717069655257060992658440577, 906694436769665430586882, 4722366482869645219844, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2341]
theorem treeEq2340 : B2340.tree = HexagonCover.NBand.M6900_7100.SplitData.node2340 := by
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
  · exact treeEq2341

def B2339 : Block := .branch 157 ![10384593717069655257060992658440577, 906694436769665430586882, 4722366482869645219844, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2340, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2339 : B2339.tree = HexagonCover.NBand.M6900_7100.SplitData.node2339 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2340
  · rfl
  · rfl

def B2338 : Block := .branch 171 ![10384593717070245552871351364092289, 906842010722255106999810, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), B2339, (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq2338 : B2338.tree = HexagonCover.NBand.M6900_7100.SplitData.node2338 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2339
  · rfl

def B2315 : Block := .branch 86 ![10384596192950324123631901162340737, 906842010722255106999810, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2316, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B2338]
theorem treeEq2315 : B2315.tree = HexagonCover.NBand.M6900_7100.SplitData.node2315 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2316
  · rfl
  · rfl
  · exact treeEq2338

theorem accepted2315 : B2315.accepted = true := by decide +kernel
theorem checked2315 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2315 (maskNeeds ![10384596192950324123631901162340737, 906842010722255106999810, 33093458868234935605252, 38687987410909568413229064, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840]) := by
  rw [← treeEq2315]
  exact B2315.sound accepted2315
#print axioms checked2315

def B2365 : Block := .branch 159 ![2993155353253689176483681838603404083058343254425985, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 993).pointIds 993), (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq2365 : B2365.tree = HexagonCover.NBand.M6900_7100.SplitData.node2365 := by
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
  · rfl

def B2364 : Block := .branch 171 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![B2365, (.leaf 1 (Common.fact 954).pointIds 954), (.leaf 2 (Common.fact 955).pointIds 955), (.leaf 3 (Common.fact 912).pointIds 912), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 992).pointIds 992)]
theorem treeEq2364 : B2364.tree = HexagonCover.NBand.M6900_7100.SplitData.node2364 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2365
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2363 : Block := .branch 75 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B2364, (.leaf 3 (Common.fact 987).pointIds 987), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 990).pointIds 990)]
theorem treeEq2363 : B2363.tree = HexagonCover.NBand.M6900_7100.SplitData.node2363 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2364
  · rfl
  · rfl
  · rfl
  · rfl

def B2362 : Block := .branch 118 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), (.leaf 2 (Common.fact 283).pointIds 283), (.leaf 3 (Common.fact 847).pointIds 847), B2363, (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 984).pointIds 984)]
theorem treeEq2362 : B2362.tree = HexagonCover.NBand.M6900_7100.SplitData.node2362 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2363
  · rfl
  · rfl

def B2361 : Block := .branch 163 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713798411207534900514558122625143221304524816, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 983).pointIds 983), (.leaf 5 (Common.fact 262).pointIds 262), B2362]
theorem treeEq2361 : B2361.tree = HexagonCover.NBand.M6900_7100.SplitData.node2361 := by
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
  · exact treeEq2362

def B2360 : Block := .branch 128 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713798070925167979576094659250535789536313360, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), (.leaf 3 (Common.fact 965).pointIds 965), B2361, (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 982).pointIds 982)]
theorem treeEq2360 : B2360.tree = HexagonCover.NBand.M6900_7100.SplitData.node2360 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2361
  · rfl
  · rfl

def B2359 : Block := .branch 165 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713798070925167979576094659250535789536313360, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 981).pointIds 981), B2360, (.leaf 0 [] 0)]
theorem treeEq2359 : B2359.tree = HexagonCover.NBand.M6900_7100.SplitData.node2359 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2360
  · rfl

def B2358 : Block := .branch 167 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713798070925167979576094659250535789536313360, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 980).pointIds 980), B2359, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2358 : B2358.tree = HexagonCover.NBand.M6900_7100.SplitData.node2358 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2359
  · rfl

def B2357 : Block := .branch 137 ![2535301200456458802993406411137, 737941821641931621890, 33093458868234935605252, 5986310706507378352962293190865135114756535290454024, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), (.leaf 3 (Common.fact 806).pointIds 806), B2358, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2357 : B2357.tree = HexagonCover.NBand.M6900_7100.SplitData.node2357 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2358
  · rfl
  · rfl

def B2356 : Block := .branch 172 ![10387131494150190286624535863099777, 737941821641931621890, 33093458868234935605252, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), B2357, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq2356 : B2356.tree = HexagonCover.NBand.M6900_7100.SplitData.node2356 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2357
  · rfl
  · rfl
  · rfl

def B2355 : Block := .branch 142 ![10387131494150190286624535863099777, 737941821641931621890, 33093458868234935605252, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B2356]
theorem treeEq2355 : B2355.tree = HexagonCover.NBand.M6900_7100.SplitData.node2355 := by
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
  · exact treeEq2356

def B2354 : Block := .branch 166 ![10387131494150190286624535863099777, 737941821641931621890, 33093458868234935605252, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 21778071483256974387270895952471420043328] ![B2355, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq2354 : B2354.tree = HexagonCover.NBand.M6900_7100.SplitData.node2354 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2353 : Block := .branch 151 ![10387131494150190286624535863099777, 737941821641931621890, 33093458868234935605252, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B2354, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2353 : B2353.tree = HexagonCover.NBand.M6900_7100.SplitData.node2353 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2354
  · rfl

theorem accepted2353 : B2353.accepted = true := by decide +kernel
theorem checked2353 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2353 (maskNeeds ![10387131494150190286624535863099777, 737941821641931621890, 33093458868234935605252, 116059239866245835594424328, 713623846353304459082801411451530724212047888, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq2353]
  exact B2353.sound accepted2353
#print axioms checked2353

end HexagonCover.NBand.M6900_7100.SplitTree.Run0030
