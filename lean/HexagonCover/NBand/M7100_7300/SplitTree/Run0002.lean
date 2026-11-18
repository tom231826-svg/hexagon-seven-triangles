import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0089_0090 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0090 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0001.checked0090
def B0218 : Block := .branch 170 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520570664500254341332505485320, 11692015886240373486475925012121775021448669265936, 43556142965880123323311949751266331459616, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 626).pointIds 626), (.leaf 1 (Common.fact 507).pointIds 507), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 499).pointIds 499), (.leaf 4 (Common.fact 627).pointIds 627), (.leaf 5 (Common.fact 523).pointIds 523), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M7100_7300.SplitData.node0218 := by
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

def B0217 : Block := .branch 108 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 43556142965880123323311949751266331459616, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0218, (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M7100_7300.SplitData.node0217 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0218
  · rfl
  · rfl

def B0216 : Block := .branch 119 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 43556142965880123323311949751266331459616, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0217, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M7100_7300.SplitData.node0216 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0217
  · rfl
  · rfl

def B0215 : Block := .branch 129 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 43556142965880123323311949751266331459616, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), B0216, (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M7100_7300.SplitData.node0215 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl

def B0214 : Block := .branch 135 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 174224571863520609350126482009466096082952, 11692015886240373161957371353695048238292648689680, 393248, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0215, (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M7100_7300.SplitData.node0214 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215
  · rfl

def B0213 : Block := .branch 137 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692015886240373161957371353695048238292648689680, 393248, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), B0214, (.leaf 4 (Common.fact 621).pointIds 621), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M7100_7300.SplitData.node0213 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0214
  · rfl
  · rfl
  · rfl

def B0212 : Block := .branch 141 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0213, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M7100_7300.SplitData.node0212 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0213
  · rfl
  · rfl

def B0211 : Block := .branch 144 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0212, (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M7100_7300.SplitData.node0211 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0212
  · rfl

def B0210 : Block := .branch 128 ![374144419156711147060143317175368453031918731002241, 618970019642691236961191426, 77919046967349146032132, 116056878683004400771817480, 11692013098647223345629478661730264157247460442128, 393248, 5596964371115915390318226081821731633758272] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0211, (.leaf 4 (Common.fact 617).pointIds 617), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M7100_7300.SplitData.node0210 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0211
  · rfl
  · rfl
  · rfl

def B0209 : Block := .branch 168 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 11692726722493576325570007804714988904815651815440, 393248, 5596964371115915390318226081821731633758272] ![B0210, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M7100_7300.SplitData.node0209 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0210
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0208 : Block := .branch 142 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 11692726722493576325570007804714988904815651815440, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 150).pointIds 150), B0209]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M7100_7300.SplitData.node0208 := by
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
  · exact treeEq0209

def B0207 : Block := .branch 163 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0208, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M7100_7300.SplitData.node0207 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0208
  · rfl
  · rfl

def B0089 : Block := .branch 91 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0089_0090, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0207]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M7100_7300.SplitData.node0089 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0207

theorem accepted0089 : B0089.accepted = true := by decide +kernel
theorem checked0089 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0089 (maskNeeds ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0089]
  exact B0089.sound accepted0089
#print axioms checked0089

def B0239 : Block := .branch 163 ![385, 1538, 6148, 24584, 2993155356215506898160994923388160207341460360626192, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M7100_7300.SplitData.node0239 := by
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
  · rfl

def B0238 : Block := .branch 137 ![385, 1538, 6148, 1496577676626844588240573307387100039795808514629640, 2993155356041282326297474430094912408336395036360720, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), (.leaf 3 (Common.fact 671).pointIds 671), B0239, (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 0 [] 0)]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M7100_7300.SplitData.node0238 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0239
  · rfl
  · rfl

def B0237 : Block := .branch 77 ![385, 1538, 2923003274661805836407369743351613006661011118084, 1496577676626844588240573307387100039795808514629640, 2993155356041282326297474430094912408336395036360720, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 291).pointIds 291), B0238, (.leaf 2 (Common.fact 669).pointIds 669), (.leaf 3 (Common.fact 293).pointIds 293), (.leaf 4 (Common.fact 294).pointIds 294), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M7100_7300.SplitData.node0237 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0238
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0236 : Block := .branch 161 ![385, 1538, 77919046967349146032132, 1496577676626844588240573307387100039795808514629640, 2993155356041282326297474430094912408336395036360720, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), B0237, (.leaf 3 (Common.fact 667).pointIds 667), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M7100_7300.SplitData.node0236 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0237
  · rfl
  · rfl
  · rfl
  · rfl

def B0235 : Block := .branch 170 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 2993155357086629757478597389854399202366786981953552, 43556142965880123323311949751266331459616, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 501).pointIds 501), B0236, (.leaf 4 (Common.fact 645).pointIds 645), (.leaf 5 (Common.fact 523).pointIds 523), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M7100_7300.SplitData.node0235 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl
  · rfl
  · rfl

def B0234 : Block := .branch 172 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 2993155357086629757478597389854399202366786981953552, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 661).pointIds 661), (.leaf 1 (Common.fact 662).pointIds 662), (.leaf 2 (Common.fact 609).pointIds 609), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 665).pointIds 665), B0235]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M7100_7300.SplitData.node0234 := by
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
  · exact treeEq0235

def B0233 : Block := .branch 171 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 656).pointIds 656), (.leaf 1 (Common.fact 657).pointIds 657), (.leaf 2 (Common.fact 588).pointIds 588), (.leaf 3 (Common.fact 658).pointIds 658), B0234, (.leaf 5 (Common.fact 659).pointIds 659), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M7100_7300.SplitData.node0233 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl
  · rfl

def B0232 : Block := .branch 135 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0233, (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M7100_7300.SplitData.node0232 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0233
  · rfl

def B0231 : Block := .branch 138 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 3484491437270409865864955980101306485407760, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0232, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M7100_7300.SplitData.node0231 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0232
  · rfl
  · rfl

def B0230 : Block := .branch 139 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0231, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M7100_7300.SplitData.node0230 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231
  · rfl
  · rfl

def B0229 : Block := .branch 140 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0230, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M7100_7300.SplitData.node0229 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl

def B0228 : Block := .branch 141 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 98320, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0229, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M7100_7300.SplitData.node0228 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0229
  · rfl
  · rfl

def B0227 : Block := .branch 144 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 98320, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0228, (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M7100_7300.SplitData.node0227 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl

theorem accepted0227 : B0227.accepted = true := by decide +kernel
theorem checked0227 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0227 (maskNeeds ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 98320, 393248, 21778071483257361167975308907893002600512]) := by
  rw [← treeEq0227]
  exact B0227.sound accepted0227
#print axioms checked0227

def B0286 : Block := .branch 171 ![10384596192949733827821542456689025, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 5986310706855827496689334061392390846520830344658960, 393248, 1497308427467968675916457049781972541454463670943808] ![(.leaf 0 (Common.fact 736).pointIds 736), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 738).pointIds 738), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M7100_7300.SplitData.node0286 := by
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

def B0285 : Block := .branch 172 ![10384596192949733827821542456689025, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 1497308427467968675916457049781972541454463670943808] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 663).pointIds 663), B0286, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 735).pointIds 735)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M7100_7300.SplitData.node0285 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl
  · rfl

def B0284 : Block := .branch 159 ![374144419156732430284968927313896370296922002424193, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 1496577676649303224457355207365614399944635704672320] ![(.leaf 0 (Common.fact 733).pointIds 733), (.leaf 1 (Common.fact 734).pointIds 734), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), B0285]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M7100_7300.SplitData.node0284 := by
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
  · exact treeEq0285

def B0283 : Block := .branch 124 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 1496577676649303224457355207365614399944635704672320] ![B0284, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 732).pointIds 732)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M7100_7300.SplitData.node0283 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0284
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0282 : Block := .branch 135 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 1496577676649303224457355207365614399944635704672320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 419).pointIds 419), B0283, (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M7100_7300.SplitData.node0282 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283
  · rfl

def B0281 : Block := .branch 138 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 1496577676649303224457355207365614399944635704672320] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0282, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M7100_7300.SplitData.node0281 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282
  · rfl
  · rfl

def B0280 : Block := .branch 139 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 1496577676649303224457355207365614399944635704672320] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0281, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M7100_7300.SplitData.node0280 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0281
  · rfl
  · rfl

def B0279 : Block := .branch 140 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 1496577676649303224457355207365614399944635704672320] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0280, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M7100_7300.SplitData.node0279 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280
  · rfl
  · rfl

def B0278 : Block := .branch 141 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 1496577676649303224457355207365614399944635704672320] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0279, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M7100_7300.SplitData.node0278 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0279
  · rfl
  · rfl

def B0277 : Block := .branch 129 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), B0278]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M7100_7300.SplitData.node0277 := by
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
  · exact treeEq0278

def B0276 : Block := .branch 130 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 559).pointIds 559), (.leaf 1 (Common.fact 560).pointIds 560), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 562).pointIds 562), (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 564).pointIds 564), B0277]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M7100_7300.SplitData.node0276 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0277

def B0275 : Block := .branch 89 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676651344918658880838146394647589226313941056] ![(.leaf 0 (Common.fact 92).pointIds 92), B0276, (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M7100_7300.SplitData.node0275 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0276
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0274 : Block := .branch 131 ![374144419156711162637036368659929909383957516910977, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 548).pointIds 548), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 550).pointIds 550), (.leaf 3 (Common.fact 551).pointIds 551), (.leaf 4 (Common.fact 552).pointIds 552), (.leaf 5 (Common.fact 553).pointIds 553), B0275]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M7100_7300.SplitData.node0274 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0275

def B0273 : Block := .branch 112 ![374144419156711157444739510125102280853461187690881, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142809100417914887019628593216] ![B0274, (.leaf 1 (Common.fact 437).pointIds 437), (.leaf 2 (Common.fact 438).pointIds 438), (.leaf 3 (Common.fact 439).pointIds 439), (.leaf 4 (Common.fact 440).pointIds 440), (.leaf 5 (Common.fact 441).pointIds 441), (.leaf 6 (Common.fact 725).pointIds 725)]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M7100_7300.SplitData.node0273 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0274
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0272 : Block := .branch 163 ![374144419156711157444739510125102280853461187690881, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0273]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M7100_7300.SplitData.node0272 := by
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
  · exact treeEq0273

def B0271 : Block := .branch 165 ![374144419156711157444739510125102280853461187690881, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0272, (.leaf 0 [] 0)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M7100_7300.SplitData.node0271 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0272
  · rfl

def B0270 : Block := .branch 167 ![374144419156711157444739510125102280853461187690881, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0271, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M7100_7300.SplitData.node0270 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0271
  · rfl

def B0269 : Block := .branch 142 ![374144419156711157444739510125102280853461187690881, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0270, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M7100_7300.SplitData.node0269 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0270
  · rfl
  · rfl

def B0268 : Block := .branch 144 ![374144419156711157444739510125102280853461187690881, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513330438687650729772168249408] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0269, (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M7100_7300.SplitData.node0268 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0269
  · rfl

def B0267 : Block := .branch 168 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513330438687650729772168249408] ![B0268, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M7100_7300.SplitData.node0267 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0268
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0267 : B0267.accepted = true := by decide +kernel
theorem checked0267 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0267 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513330438687650729772168249408]) := by
  rw [← treeEq0267]
  exact B0267.sound accepted0267
#print axioms checked0267

def B0263 : Block := .branch 79 ![374144419156732414710611177030381668558235328577921, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 717).pointIds 717), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M7100_7300.SplitData.node0263 := by
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

def B0262 : Block := .branch 159 ![374144419156732414710611177030381668558235328577921, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 714).pointIds 714), B0263, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M7100_7300.SplitData.node0262 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0263
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0261 : Block := .branch 124 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B0262, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M7100_7300.SplitData.node0261 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0262
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0260 : Block := .branch 128 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0261, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M7100_7300.SplitData.node0260 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0261
  · rfl
  · rfl
  · rfl

def B0259 : Block := .branch 75 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 5846006549323611672814778016491359746757320794120, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0260, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M7100_7300.SplitData.node0259 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0260
  · rfl
  · rfl
  · rfl
  · rfl

def B0258 : Block := .branch 162 ![374144419156711147062678618376415207645270843064705, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0259, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M7100_7300.SplitData.node0258 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0259
  · rfl
  · rfl
  · rfl

def B0257 : Block := .branch 172 ![374144419156711157447274811326149035466813299753345, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B0258]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M7100_7300.SplitData.node0257 := by
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
  · exact treeEq0258

def B0256 : Block := .branch 151 ![374144419156711157447274811326149035466813299753345, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0257, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M7100_7300.SplitData.node0256 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0257
  · rfl
  · rfl

def B0255 : Block := .branch 132 ![374144419156711157447274811326149035466813299753345, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0256]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M7100_7300.SplitData.node0255 := by
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
  · exact treeEq0256

def B0254 : Block := .branch 78 ![374144419156711157447274811326149035466813299753345, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B0255, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M7100_7300.SplitData.node0254 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0255
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0253 : Block := .branch 101 ![374144419156711157444739510125692576663819893342593, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![B0254, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M7100_7300.SplitData.node0253 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0254
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0252 : Block := .branch 168 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![B0253, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M7100_7300.SplitData.node0252 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0253
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0251 : Block := .branch 133 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0252]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M7100_7300.SplitData.node0251 := by
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
  · exact treeEq0252

def B0250 : Block := .branch 157 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0251, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M7100_7300.SplitData.node0250 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0251
  · rfl
  · rfl

def B0249 : Block := .branch 169 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B0250, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M7100_7300.SplitData.node0249 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0250
  · rfl

theorem accepted0249 : B0249.accepted = true := by decide +kernel
theorem checked0249 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0249 (maskNeeds ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq0249]
  exact B0249.sound accepted0249
#print axioms checked0249

def Tip0085_0089 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0089 ![385, 618970020002979207150831106, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0089
def Tip0085_0227 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0227 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 38685626227668133590622216, 98320, 393248, 21778071483257361167975308907893002600512] checked0227
def B0226 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 9408126880630106637835381146273527510433808, 393248, 1496577676648622659723514104075654340366529656782912] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 648).pointIds 648), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M7100_7300.SplitData.node0226 := by
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

def B0225 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 1496577676648622659723514104075654340366529656782912] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0226, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M7100_7300.SplitData.node0225 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0226
  · rfl
  · rfl

def B0224 : Block := .branch 170 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 116056878683004400771817480, 3832940580997450852451451578111437133938704, 22300745198530623141535718272648361506373664, 21778071482940835374180528238854732775488] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 645).pointIds 645), (.leaf 5 (Common.fact 646).pointIds 646), B0225]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M7100_7300.SplitData.node0224 := by
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
  · exact treeEq0225

def B0223 : Block := .branch 138 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 116056878683004400771817480, 3484491437270409865864955980101306485407760, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0224, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M7100_7300.SplitData.node0223 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · rfl
  · rfl

def B0222 : Block := .branch 139 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 116056878683004400771817480, 2787593149816327892691964784081045188345872, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0223, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M7100_7300.SplitData.node0222 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0223
  · rfl
  · rfl

def B0221 : Block := .branch 140 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 116056878683004400771817480, 2787593149816327892691964784081045188345872, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0222, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M7100_7300.SplitData.node0221 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0222
  · rfl
  · rfl

def B0220 : Block := .branch 141 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 116056878683004400771817480, 98320, 22300745198530623141535718272648361506373664, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0221, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M7100_7300.SplitData.node0220 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0221
  · rfl
  · rfl

def B0219 : Block := .branch 144 ![1208925819614629174706561, 302231526962350843233794, 77919046967349146032132, 116056878683004400771817480, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0220, (.leaf 6 (Common.fact 139).pointIds 139)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M7100_7300.SplitData.node0219 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0220
  · rfl

def B0088 : Block := .branch 89 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 92).pointIds 92), Tip0085_0089, (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), B0219]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M7100_7300.SplitData.node0088 := by
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
  · exact treeEq0219

def B0087 : Block := .branch 86 ![1208925819614629174706561, 302231815192726994945538, 77937529740219874547716, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0088, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), Tip0085_0227]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M7100_7300.SplitData.node0087 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · rfl
  · rfl
  · rfl

def B0241 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M7100_7300.SplitData.node0241 := by
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

def B0240 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0241, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M7100_7300.SplitData.node0240 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0241
  · rfl
  · rfl

def B0086 : Block := .branch 80 ![385, 302231815192726994945538, 77937529740219874547716, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0087, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0240]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M7100_7300.SplitData.node0086 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0087
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0240

def B0244 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 158).pointIds 158)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M7100_7300.SplitData.node0244 := by
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

def B0243 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0244, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 151).pointIds 151)]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M7100_7300.SplitData.node0243 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0244
  · rfl
  · rfl

def B0242 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0243, (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M7100_7300.SplitData.node0242 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0243
  · rfl

def B0085 : Block := .branch 78 ![385, 360289069701268994, 77937529740219874547716, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B0086, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0242]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M7100_7300.SplitData.node0085 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0086
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0242

theorem accepted0085 : B0085.accepted = true := by decide +kernel
theorem checked0085 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0085 (maskNeeds ![385, 360289069701268994, 77937529740219874547716, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0085]
  exact B0085.sound accepted0085
#print axioms checked0085

end HexagonCover.NBand.M7100_7300.SplitTree.Run0002
