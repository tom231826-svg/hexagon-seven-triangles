import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0090
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0091
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B6536 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq6536 : B6536.tree = HexagonCover.NBand.M8500_8700.SplitData.node6536 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6535 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6536, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq6535 : B6535.tree = HexagonCover.NBand.M8500_8700.SplitData.node6535 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6536
  · rfl

def B6534 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6535]
theorem treeEq6534 : B6534.tree = HexagonCover.NBand.M8500_8700.SplitData.node6534 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6535

def B6533 : Block := .branch 172 ![1238242270740283932192801153, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6534, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq6533 : B6533.tree = HexagonCover.NBand.M8500_8700.SplitData.node6533 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6534
  · rfl
  · rfl
  · rfl

def B6532 : Block := .branch 159 ![5193565747377326598215925225226625, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 1003).pointIds 1003), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6533]
theorem treeEq6532 : B6532.tree = HexagonCover.NBand.M8500_8700.SplitData.node6532 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6533

def B6542 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq6542 : B6542.tree = HexagonCover.NBand.M8500_8700.SplitData.node6542 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6541 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6542, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq6541 : B6541.tree = HexagonCover.NBand.M8500_8700.SplitData.node6541 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6542
  · rfl

def B6540 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6541]
theorem treeEq6540 : B6540.tree = HexagonCover.NBand.M8500_8700.SplitData.node6540 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6541

def B6539 : Block := .branch 172 ![1238242270740283932192801153, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6540, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq6539 : B6539.tree = HexagonCover.NBand.M8500_8700.SplitData.node6539 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6540
  · rfl
  · rfl
  · rfl

def B6538 : Block := .branch 159 ![10385862605912154226746421554446721, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 1004).pointIds 1004), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6539]
theorem treeEq6538 : B6538.tree = HexagonCover.NBand.M8500_8700.SplitData.node6538 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6539

def B6546 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq6546 : B6546.tree = HexagonCover.NBand.M8500_8700.SplitData.node6546 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6545 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6546, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq6545 : B6545.tree = HexagonCover.NBand.M8500_8700.SplitData.node6545 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6546
  · rfl

def B6544 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6545]
theorem treeEq6544 : B6544.tree = HexagonCover.NBand.M8500_8700.SplitData.node6544 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6545

def B6543 : Block := .branch 172 ![1238242270740283932192801153, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6544, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq6543 : B6543.tree = HexagonCover.NBand.M8500_8700.SplitData.node6543 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6544
  · rfl
  · rfl
  · rfl

def B6537 : Block := .branch 113 ![1268888842498969685428896006529, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B6538, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B6543]
theorem treeEq6537 : B6537.tree = HexagonCover.NBand.M8500_8700.SplitData.node6537 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6538
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6543

def B6531 : Block := .branch 112 ![1268888842498969685428896006529, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B6532, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B6537]
theorem treeEq6531 : B6531.tree = HexagonCover.NBand.M8500_8700.SplitData.node6531 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6537

def B6548 : Block := .branch 168 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 978).pointIds 978), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq6548 : B6548.tree = HexagonCover.NBand.M8500_8700.SplitData.node6548 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6547 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6548, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq6547 : B6547.tree = HexagonCover.NBand.M8500_8700.SplitData.node6547 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6548
  · rfl

def B6530 : Block := .branch 109 ![1268888842498969685428896006529, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B6531, (.leaf 5 (Common.fact 294).pointIds 294), B6547]
theorem treeEq6530 : B6530.tree = HexagonCover.NBand.M8500_8700.SplitData.node6530 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6531
  · rfl
  · exact treeEq6547

theorem accepted6530 : B6530.accepted = true := by decide +kernel
theorem checked6530 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6530 (maskNeeds ![1268888842498969685428896006529, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq6530]
  exact B6530.sound accepted6530
#print axioms checked6530

def Tip6488_6492 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6492 ![1269507812518612375566345568641, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] HexagonCover.NBand.M8500_8700.SplitTree.Run0090.checked6492
def B6515 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6515 : B6515.tree = HexagonCover.NBand.M8500_8700.SplitData.node6515 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6514 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6515, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6514 : B6514.tree = HexagonCover.NBand.M8500_8700.SplitData.node6514 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6515
  · rfl

def B6513 : Block := .branch 163 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B6514]
theorem treeEq6513 : B6513.tree = HexagonCover.NBand.M8500_8700.SplitData.node6513 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6514

def B6512 : Block := .branch 165 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B6513, (.leaf 0 [] 0)]
theorem treeEq6512 : B6512.tree = HexagonCover.NBand.M8500_8700.SplitData.node6512 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6513
  · rfl

def B6511 : Block := .branch 167 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B6512, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6511 : B6511.tree = HexagonCover.NBand.M8500_8700.SplitData.node6511 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6512
  · rfl

def B6491 : Block := .branch 108 ![1269507812518612375566345568641, 151115729774546960516610, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip6488_6492, B6511, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6491 : B6491.tree = HexagonCover.NBand.M8500_8700.SplitData.node6491 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6511
  · rfl
  · rfl

def B6518 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6518 : B6518.tree = HexagonCover.NBand.M8500_8700.SplitData.node6518 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6517 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6518, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq6517 : B6517.tree = HexagonCover.NBand.M8500_8700.SplitData.node6517 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6518
  · rfl
  · rfl
  · rfl

def B6516 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 362715524816251709573568516, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B6517]
theorem treeEq6516 : B6516.tree = HexagonCover.NBand.M8500_8700.SplitData.node6516 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6517

def B6490 : Block := .branch 88 ![1269507812518612375566345568641, 151115729774546960516610, 53230514994906640848787460, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 997).pointIds 997), B6491, B6516, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6490 : B6490.tree = HexagonCover.NBand.M8500_8700.SplitData.node6490 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6491
  · exact treeEq6516
  · rfl
  · rfl
  · rfl
  · rfl

def B6520 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6520 : B6520.tree = HexagonCover.NBand.M8500_8700.SplitData.node6520 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6519 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6520, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq6519 : B6519.tree = HexagonCover.NBand.M8500_8700.SplitData.node6519 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6520
  · rfl
  · rfl
  · rfl

def B6489 : Block := .branch 100 ![1857212290382974069642363265, 151115729774546960516610, 53230514994906640848787460, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B6490, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B6519]
theorem treeEq6489 : B6489.tree = HexagonCover.NBand.M8500_8700.SplitData.node6489 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6490
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6519

def B6525 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6525 : B6525.tree = HexagonCover.NBand.M8500_8700.SplitData.node6525 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6524 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6525, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6524 : B6524.tree = HexagonCover.NBand.M8500_8700.SplitData.node6524 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6525
  · rfl

def B6523 : Block := .branch 163 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B6524]
theorem treeEq6523 : B6523.tree = HexagonCover.NBand.M8500_8700.SplitData.node6523 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6524

def B6522 : Block := .branch 165 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B6523, (.leaf 0 [] 0)]
theorem treeEq6522 : B6522.tree = HexagonCover.NBand.M8500_8700.SplitData.node6522 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6523
  · rfl

def B6521 : Block := .branch 167 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B6522, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6521 : B6521.tree = HexagonCover.NBand.M8500_8700.SplitData.node6521 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6522
  · rfl

def B6488 : Block := .branch 98 ![1857212290382974069642363265, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6489, B6521, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6488 : B6488.tree = HexagonCover.NBand.M8500_8700.SplitData.node6488 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6489
  · exact treeEq6521
  · rfl
  · rfl

theorem accepted6488 : B6488.accepted = true := by decide +kernel
theorem checked6488 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6488 (maskNeeds ![1857212290382974069642363265, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6488]
  exact B6488.sound accepted6488
#print axioms checked6488

def Tip6487_6530 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6530 ![1268888842498969685428896006529, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] checked6530
def Tip6487_6488 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6488 ![1857212290382974069642363265, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] checked6488
def B6553 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6553 : B6553.tree = HexagonCover.NBand.M8500_8700.SplitData.node6553 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6552 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6553, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6552 : B6552.tree = HexagonCover.NBand.M8500_8700.SplitData.node6552 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6553
  · rfl

def B6551 : Block := .branch 163 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B6552]
theorem treeEq6551 : B6551.tree = HexagonCover.NBand.M8500_8700.SplitData.node6551 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6552

def B6550 : Block := .branch 165 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B6551, (.leaf 0 [] 0)]
theorem treeEq6550 : B6550.tree = HexagonCover.NBand.M8500_8700.SplitData.node6550 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6551
  · rfl

def B6549 : Block := .branch 167 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B6550, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6549 : B6549.tree = HexagonCover.NBand.M8500_8700.SplitData.node6549 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6550
  · rfl

def B6529 : Block := .branch 108 ![1268888842498969685428896006529, 151115729774546960516610, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip6487_6530, B6549, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6529 : B6529.tree = HexagonCover.NBand.M8500_8700.SplitData.node6529 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6549
  · rfl
  · rfl

def B6556 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6556 : B6556.tree = HexagonCover.NBand.M8500_8700.SplitData.node6556 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6555 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6556, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq6555 : B6555.tree = HexagonCover.NBand.M8500_8700.SplitData.node6555 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6556
  · rfl
  · rfl
  · rfl

def B6554 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 362715524816251709573568516, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B6555]
theorem treeEq6554 : B6554.tree = HexagonCover.NBand.M8500_8700.SplitData.node6554 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6555

def B6528 : Block := .branch 88 ![1268888842498969685428896006529, 151115729774546960516610, 53230514994906640848787460, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 1002).pointIds 1002), B6529, B6554, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6528 : B6528.tree = HexagonCover.NBand.M8500_8700.SplitData.node6528 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6529
  · exact treeEq6554
  · rfl
  · rfl
  · rfl
  · rfl

def B6558 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6558 : B6558.tree = HexagonCover.NBand.M8500_8700.SplitData.node6558 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6557 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6558, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq6557 : B6557.tree = HexagonCover.NBand.M8500_8700.SplitData.node6557 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6558
  · rfl
  · rfl
  · rfl

def B6527 : Block := .branch 100 ![1238242270740283932192801153, 151115729774546960516610, 53230514994906640848787460, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B6528, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B6557]
theorem treeEq6527 : B6527.tree = HexagonCover.NBand.M8500_8700.SplitData.node6527 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6528
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6557

def B6563 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6563 : B6563.tree = HexagonCover.NBand.M8500_8700.SplitData.node6563 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6562 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6563, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6562 : B6562.tree = HexagonCover.NBand.M8500_8700.SplitData.node6562 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6563
  · rfl

def B6561 : Block := .branch 163 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B6562]
theorem treeEq6561 : B6561.tree = HexagonCover.NBand.M8500_8700.SplitData.node6561 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6562

def B6560 : Block := .branch 165 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B6561, (.leaf 0 [] 0)]
theorem treeEq6560 : B6560.tree = HexagonCover.NBand.M8500_8700.SplitData.node6560 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6561
  · rfl

def B6559 : Block := .branch 167 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B6560, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6559 : B6559.tree = HexagonCover.NBand.M8500_8700.SplitData.node6559 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6560
  · rfl

def B6526 : Block := .branch 98 ![1238242270740283932192801153, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6527, B6559, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6526 : B6526.tree = HexagonCover.NBand.M8500_8700.SplitData.node6526 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6527
  · exact treeEq6559
  · rfl
  · rfl

def B6487 : Block := .branch 89 ![1238242270740283932192801153, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![Tip6487_6488, B6526, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6487 : B6487.tree = HexagonCover.NBand.M8500_8700.SplitData.node6487 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6487 : B6487.accepted = true := by decide +kernel
theorem checked6487 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6487 (maskNeeds ![1238242270740283932192801153, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6487]
  exact B6487.sound accepted6487
#print axioms checked6487

def B6595 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq6595 : B6595.tree = HexagonCover.NBand.M8500_8700.SplitData.node6595 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6594 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6595, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq6594 : B6594.tree = HexagonCover.NBand.M8500_8700.SplitData.node6594 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6595
  · rfl

def B6593 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6594]
theorem treeEq6593 : B6593.tree = HexagonCover.NBand.M8500_8700.SplitData.node6593 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6594

def B6600 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq6600 : B6600.tree = HexagonCover.NBand.M8500_8700.SplitData.node6600 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6599 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6600, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq6599 : B6599.tree = HexagonCover.NBand.M8500_8700.SplitData.node6599 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6600
  · rfl

def B6598 : Block := .branch 163 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B6599]
theorem treeEq6598 : B6598.tree = HexagonCover.NBand.M8500_8700.SplitData.node6598 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6599

def B6597 : Block := .branch 165 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B6598, (.leaf 0 [] 0)]
theorem treeEq6597 : B6597.tree = HexagonCover.NBand.M8500_8700.SplitData.node6597 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6598
  · rfl

def B6596 : Block := .branch 167 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B6597, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6596 : B6596.tree = HexagonCover.NBand.M8500_8700.SplitData.node6596 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6597
  · rfl

def B6592 : Block := .branch 129 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B6593, B6596, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq6592 : B6592.tree = HexagonCover.NBand.M8500_8700.SplitData.node6592 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6593
  · exact treeEq6596
  · rfl
  · rfl

def B6605 : Block := .branch 160 ![385, 151115729774546960516610, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq6605 : B6605.tree = HexagonCover.NBand.M8500_8700.SplitData.node6605 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6604 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), B6605, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq6604 : B6604.tree = HexagonCover.NBand.M8500_8700.SplitData.node6604 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6605
  · rfl
  · rfl
  · rfl
  · rfl

def B6603 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), B6604, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq6603 : B6603.tree = HexagonCover.NBand.M8500_8700.SplitData.node6603 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6604
  · rfl
  · rfl
  · rfl

def B6602 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B6603]
theorem treeEq6602 : B6602.tree = HexagonCover.NBand.M8500_8700.SplitData.node6602 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6603

def B6601 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6602, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq6601 : B6601.tree = HexagonCover.NBand.M8500_8700.SplitData.node6601 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6602
  · rfl

def B6591 : Block := .branch 121 ![1238242270740283932192801153, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B6592, (.leaf 5 (Common.fact 319).pointIds 319), B6601]
theorem treeEq6591 : B6591.tree = HexagonCover.NBand.M8500_8700.SplitData.node6591 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6592
  · rfl
  · exact treeEq6601

theorem accepted6591 : B6591.accepted = true := by decide +kernel
theorem checked6591 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6591 (maskNeeds ![1238242270740283932192801153, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq6591]
  exact B6591.sound accepted6591
#print axioms checked6591

end HexagonCover.NBand.M8500_8700.SplitTree.Run0091
