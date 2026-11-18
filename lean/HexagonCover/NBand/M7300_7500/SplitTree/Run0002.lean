import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B0230 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692015886240373161957371353695048238292648689680, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 607).pointIds 607), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M7300_7500.SplitData.node0230 := by
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

def B0229 : Block := .branch 163 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0230, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M7300_7500.SplitData.node0229 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl

def B0228 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0229]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M7300_7500.SplitData.node0228 := by
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
  · exact treeEq0229

def B0227 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 1496577676670400731206453392024785761878941255467040, 23384026219072518174516318491435837222387923288128] ![B0228, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M7300_7500.SplitData.node0227 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0228
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0226 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 716411439502796268421834949508828613379719184, 1496577676670400731206453392024785761878941255467040, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0227]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M7300_7500.SplitData.node0226 := by
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
  · exact treeEq0227

def B0225 : Block := .branch 169 ![385, 302231815192726994945538, 77937529740219874547716, 38685626227668133590622216, 717456786933977391381594436302859005325312016, 1496577676670400731206453392024785761878941255467040, 21778071483257361167975308907893002600512] ![B0226, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 627).pointIds 627)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M7300_7500.SplitData.node0225 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0224 : Block := .branch 170 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 38685626227668133590622216, 2993156070710476110458537918997383927114355173326864, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 596).pointIds 596), (.leaf 1 (Common.fact 597).pointIds 597), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 599).pointIds 599), B0225, (.leaf 6 (Common.fact 624).pointIds 624)]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M7300_7500.SplitData.node0224 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0225
  · rfl

def B0223 : Block := .branch 171 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 38685626227668133590622216, 717456786933977391381594436302859005325312016, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 593).pointIds 593), (.leaf 2 (Common.fact 547).pointIds 547), (.leaf 3 (Common.fact 620).pointIds 620), B0224, (.leaf 5 (Common.fact 621).pointIds 621), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M7300_7500.SplitData.node0223 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · rfl
  · rfl

def B0222 : Block := .branch 135 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 38685626227668133590622216, 717456786933977391381594436302859005325312016, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B0223, (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M7300_7500.SplitData.node0222 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0223
  · rfl

def B0221 : Block := .branch 138 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 717108337790250350395007940704848874676781072, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0222, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M7300_7500.SplitData.node0221 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0222
  · rfl
  · rfl

def B0220 : Block := .branch 139 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 716411439502796268421834949508828613379719184, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0221, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M7300_7500.SplitData.node0220 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0221
  · rfl
  · rfl

def B0219 : Block := .branch 140 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 716411439502796268421834949508828613379719184, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0220, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 611).pointIds 611)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M7300_7500.SplitData.node0219 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0220
  · rfl
  · rfl

def B0218 : Block := .branch 141 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B0219, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 610).pointIds 610)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M7300_7500.SplitData.node0218 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0219
  · rfl
  · rfl

def B0217 : Block := .branch 144 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B0218, (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M7300_7500.SplitData.node0217 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0218
  · rfl

theorem accepted0217 : B0217.accepted = true := by decide +kernel
theorem checked0217 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0217 (maskNeeds ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512]) := by
  rw [← treeEq0217]
  exact B0217.sound accepted0217
#print axioms checked0217

def Tip0086_0090 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0090 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0001.checked0090
def Tip0086_0204 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0204 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] HexagonCover.NBand.M7300_7500.SplitTree.Run0001.checked0204
def Tip0086_0217 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0217 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] checked0217
def B0203 : Block := .branch 170 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517163483403021721506235412649914022756416] ![(.leaf 0 (Common.fact 580).pointIds 580), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 587).pointIds 587)]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M7300_7500.SplitData.node0203 := by
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
  · rfl

def B0202 : Block := .branch 108 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483403021721506235412649914022756416] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0203, (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M7300_7500.SplitData.node0202 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203
  · rfl
  · rfl

def B0201 : Block := .branch 119 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483403021721506235412649914022756416] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0202, (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M7300_7500.SplitData.node0201 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl
  · rfl

def B0200 : Block := .branch 129 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863599837512640746347059640033288, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483403021721506235412649914022756416] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), B0201, (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 584).pointIds 584)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M7300_7500.SplitData.node0200 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201
  · rfl
  · rfl

def B0199 : Block := .branch 137 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 2854517163483403021721506235412649914022756416] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0200, (.leaf 4 (Common.fact 576).pointIds 576), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M7300_7500.SplitData.node0199 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl
  · rfl
  · rfl

def B0198 : Block := .branch 151 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11874700803313586210404939265819799534704452010000, 42535295865117307932921825928971419680, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 255).pointIds 255), B0199]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M7300_7500.SplitData.node0198 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0199

def B0197 : Block := .branch 157 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11692013098647223345629478661730264157247460442128, 42535295865117307932921825928971419680, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B0198, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M7300_7500.SplitData.node0197 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0198
  · rfl
  · rfl

def B0196 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 11692013098647223345629478661730264157247460442128, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0197, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M7300_7500.SplitData.node0196 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0197
  · rfl

def B0195 : Block := .branch 168 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 11692726722493576325570007804714988904815651815440, 393248, 5596964371115915699803235903166800358539328] ![B0196, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M7300_7500.SplitData.node0195 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0196
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0194 : Block := .branch 142 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 11692726722493576325570007804714988904815651815440, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 144).pointIds 144), B0195]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M7300_7500.SplitData.node0194 := by
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
  · exact treeEq0195

def B0193 : Block := .branch 163 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0194, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 582).pointIds 582)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M7300_7500.SplitData.node0193 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194
  · rfl
  · rfl

def B0089 : Block := .branch 91 ![385, 618970020002979207150831106, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0086_0090, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0193]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M7300_7500.SplitData.node0089 := by
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
  · exact treeEq0193

def B0088 : Block := .branch 89 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), B0089, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip0086_0204]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M7300_7500.SplitData.node0088 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0089
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0087 : Block := .branch 86 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0088, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), Tip0086_0217]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M7300_7500.SplitData.node0087 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · rfl
  · rfl
  · rfl

def B0232 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M7300_7500.SplitData.node0232 := by
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

def B0231 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0232, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M7300_7500.SplitData.node0231 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0232
  · rfl
  · rfl

def B0086 : Block := .branch 80 ![385, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0087, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B0231]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M7300_7500.SplitData.node0086 := by
  change Tree.branch (80 : Fin 172) _ = Tree.branch (80 : Fin 172) _
  apply congrArg (Tree.branch (80 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0087
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231

theorem accepted0086 : B0086.accepted = true := by decide +kernel
theorem checked0086 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0086 (maskNeeds ![385, 302231815192726994945538, 77937529740219874547716, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0086]
  exact B0086.sound accepted0086
#print axioms checked0086

def B0264 : Block := .branch 142 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 24114777037737969633617774127089565776794307002432] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M7300_7500.SplitData.node0264 := by
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

def B0263 : Block := .branch 159 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0264]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M7300_7500.SplitData.node0263 := by
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
  · exact treeEq0264

def B0262 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0263]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M7300_7500.SplitData.node0262 := by
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
  · exact treeEq0263

def B0261 : Block := .branch 169 ![2535301200456458802993406411137, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483256974387270895952471420043328] ![B0262, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M7300_7500.SplitData.node0261 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0262
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0260 : Block := .branch 170 ![10387131494150190286624535863099777, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B0261, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M7300_7500.SplitData.node0260 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0261
  · rfl

def B0274 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993886104094132699747706995214946331150431079104576] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 693).pointIds 693), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M7300_7500.SplitData.node0274 := by
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

def B0273 : Block := .branch 159 ![374144419156732414710611177029791372747876622926209, 737941821641931621890, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 692).pointIds 692), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0274]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M7300_7500.SplitData.node0273 := by
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
  · exact treeEq0274

def B0272 : Block := .branch 124 ![374144419156711147062678618375824911834912137412993, 737941821641931621890, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![B0273, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M7300_7500.SplitData.node0272 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0273
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0271 : Block := .branch 160 ![374144419156711147062678618375824911834912137412993, 737941821641931621890, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 689).pointIds 689), B0272, (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M7300_7500.SplitData.node0271 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0272
  · rfl
  · rfl
  · rfl
  · rfl

def B0270 : Block := .branch 75 ![374144419156711147062678618375824911834912137412993, 737941821641931621890, 6148, 5846006549323611672814855387743815083024501989384, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B0271, (.leaf 3 (Common.fact 687).pointIds 687), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M7300_7500.SplitData.node0270 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0271
  · rfl
  · rfl
  · rfl
  · rfl

def B0269 : Block := .branch 162 ![374144419156711147062678618375824911834912137412993, 737941821641931621890, 6148, 116056878683004400771817480, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0270, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M7300_7500.SplitData.node0269 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0270
  · rfl
  · rfl
  · rfl

def B0268 : Block := .branch 171 ![374144419156711157447274811325558739656454594101633, 737941821641931621890, 21287542661060822571012, 116056878683004400771817480, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0269]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M7300_7500.SplitData.node0268 := by
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
  · exact treeEq0269

def B0267 : Block := .branch 170 ![374144419156711157447274811325558739656454594101633, 737941821641931621890, 21287542661060822571012, 116056878683004400771817480, 98320, 42535295865117307932921825928971419680, 21778071807775528045697622735627440619584] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), B0268, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M7300_7500.SplitData.node0267 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0268
  · rfl
  · rfl

def B0266 : Block := .branch 125 ![374144419156711157447274811325558739656454594101633, 737941821641931621890, 21287542661060822571012, 116056878683004400771817480, 98320, 393248, 21778071807775837530707444080696165400640] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0267, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M7300_7500.SplitData.node0266 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0267
  · rfl

def B0265 : Block := .branch 168 ![10387131494150190286624535863099777, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071807775837530707444080696165400640] ![B0266, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M7300_7500.SplitData.node0265 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0266
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0259 : Block := .branch 108 ![10387131494150190286624535863099777, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0260, (.leaf 5 (Common.fact 308).pointIds 308), B0265]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M7300_7500.SplitData.node0259 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0260
  · rfl
  · exact treeEq0265

theorem accepted0259 : B0259.accepted = true := by decide +kernel
theorem checked0259 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0259 (maskNeeds ![10387131494150190286624535863099777, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384]) := by
  rw [← treeEq0259]
  exact B0259.sound accepted0259
#print axioms checked0259

def Tip0257_0259 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0259 ![10387131494150190286624535863099777, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] checked0259
def B0283 : Block := .branch 109 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M7300_7500.SplitData.node0283 := by
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

def B0282 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B0283, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M7300_7500.SplitData.node0282 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283
  · rfl
  · rfl

def B0281 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B0282, (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M7300_7500.SplitData.node0281 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282
  · rfl

def B0280 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0281]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M7300_7500.SplitData.node0280 := by
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
  · exact treeEq0281

def B0279 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B0280, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M7300_7500.SplitData.node0279 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0280
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0278 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0279]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M7300_7500.SplitData.node0278 := by
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
  · exact treeEq0279

def B0277 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B0278, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M7300_7500.SplitData.node0277 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0278
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0276 : Block := .branch 170 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B0277, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M7300_7500.SplitData.node0276 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0277
  · rfl

def B0275 : Block := .branch 171 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), B0276, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M7300_7500.SplitData.node0275 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276
  · rfl
  · rfl

def B0258 : Block := .branch 101 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![Tip0257_0259, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0275]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M7300_7500.SplitData.node0258 := by
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
  · exact treeEq0275

def B0291 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M7300_7500.SplitData.node0291 := by
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

def B0290 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0291, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M7300_7500.SplitData.node0290 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0291
  · rfl
  · rfl

def B0289 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0290]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M7300_7500.SplitData.node0289 := by
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
  · exact treeEq0290

def B0288 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B0289, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M7300_7500.SplitData.node0288 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0287 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0288]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M7300_7500.SplitData.node0287 := by
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
  · exact treeEq0288

def B0286 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![B0287, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M7300_7500.SplitData.node0286 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0287
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0285 : Block := .branch 170 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B0286, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M7300_7500.SplitData.node0285 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl

def B0284 : Block := .branch 171 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257902842300359987677594386496] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), B0285, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M7300_7500.SplitData.node0284 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0285
  · rfl
  · rfl

def B0257 : Block := .branch 89 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 86).pointIds 86), B0258, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B0284]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M7300_7500.SplitData.node0257 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0258
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0284

theorem accepted0257 : B0257.accepted = true := by decide +kernel
theorem checked0257 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0257 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384]) := by
  rw [← treeEq0257]
  exact B0257.sound accepted0257
#print axioms checked0257

end HexagonCover.NBand.M7300_7500.SplitTree.Run0002
