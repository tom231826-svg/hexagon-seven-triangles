import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0064
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B4638 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq4638 : B4638.tree = HexagonCover.NBand.M8500_8700.SplitData.node4638 := by
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

def B4637 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4638, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq4637 : B4637.tree = HexagonCover.NBand.M8500_8700.SplitData.node4637 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4638
  · rfl

def B4636 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4637]
theorem treeEq4636 : B4636.tree = HexagonCover.NBand.M8500_8700.SplitData.node4636 := by
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
  · exact treeEq4637

def B4635 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4636, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq4635 : B4635.tree = HexagonCover.NBand.M8500_8700.SplitData.node4635 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4636
  · rfl
  · rfl
  · rfl

def B4634 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B4635]
theorem treeEq4634 : B4634.tree = HexagonCover.NBand.M8500_8700.SplitData.node4634 := by
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
  · exact treeEq4635

def B4640 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq4640 : B4640.tree = HexagonCover.NBand.M8500_8700.SplitData.node4640 := by
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

def B4639 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4640, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq4639 : B4639.tree = HexagonCover.NBand.M8500_8700.SplitData.node4639 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4640
  · rfl
  · rfl
  · rfl

def B4633 : Block := .branch 144 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B4634, B4639]
theorem treeEq4633 : B4633.tree = HexagonCover.NBand.M8500_8700.SplitData.node4633 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4634
  · exact treeEq4639

def B4646 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq4646 : B4646.tree = HexagonCover.NBand.M8500_8700.SplitData.node4646 := by
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

def B4645 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4646, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq4645 : B4645.tree = HexagonCover.NBand.M8500_8700.SplitData.node4645 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4646
  · rfl

def B4644 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4645]
theorem treeEq4644 : B4644.tree = HexagonCover.NBand.M8500_8700.SplitData.node4644 := by
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
  · exact treeEq4645

def B4643 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4644, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq4643 : B4643.tree = HexagonCover.NBand.M8500_8700.SplitData.node4643 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4644
  · rfl
  · rfl
  · rfl

def B4642 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B4643]
theorem treeEq4642 : B4642.tree = HexagonCover.NBand.M8500_8700.SplitData.node4642 := by
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
  · exact treeEq4643

def B4641 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B4642, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq4641 : B4641.tree = HexagonCover.NBand.M8500_8700.SplitData.node4641 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4642
  · rfl

def B4632 : Block := .branch 142 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B4633, (.leaf 5 (Common.fact 339).pointIds 339), B4641]
theorem treeEq4632 : B4632.tree = HexagonCover.NBand.M8500_8700.SplitData.node4632 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4633
  · rfl
  · exact treeEq4641

theorem accepted4632 : B4632.accepted = true := by decide +kernel
theorem checked4632 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4632 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq4632]
  exact B4632.sound accepted4632
#print axioms checked4632

def Tip4629_4632 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node4632 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked4632
def B4651 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq4651 : B4651.tree = HexagonCover.NBand.M8500_8700.SplitData.node4651 := by
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

def B4650 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4651, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq4650 : B4650.tree = HexagonCover.NBand.M8500_8700.SplitData.node4650 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4651
  · rfl

def B4649 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B4650]
theorem treeEq4649 : B4649.tree = HexagonCover.NBand.M8500_8700.SplitData.node4649 := by
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
  · exact treeEq4650

def B4648 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B4649, (.leaf 0 [] 0)]
theorem treeEq4648 : B4648.tree = HexagonCover.NBand.M8500_8700.SplitData.node4648 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4649
  · rfl

def B4647 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B4648, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq4647 : B4647.tree = HexagonCover.NBand.M8500_8700.SplitData.node4647 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4648
  · rfl

def B4631 : Block := .branch 138 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip4629_4632, B4647, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq4631 : B4631.tree = HexagonCover.NBand.M8500_8700.SplitData.node4631 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4647
  · rfl
  · rfl

def B4657 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq4657 : B4657.tree = HexagonCover.NBand.M8500_8700.SplitData.node4657 := by
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

def B4656 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4657, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq4656 : B4656.tree = HexagonCover.NBand.M8500_8700.SplitData.node4656 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4657
  · rfl

def B4655 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4656]
theorem treeEq4655 : B4655.tree = HexagonCover.NBand.M8500_8700.SplitData.node4655 := by
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
  · exact treeEq4656

def B4654 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4655, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq4654 : B4654.tree = HexagonCover.NBand.M8500_8700.SplitData.node4654 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4655
  · rfl
  · rfl
  · rfl

def B4653 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B4654]
theorem treeEq4653 : B4653.tree = HexagonCover.NBand.M8500_8700.SplitData.node4653 := by
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
  · exact treeEq4654

def B4652 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B4653, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq4652 : B4652.tree = HexagonCover.NBand.M8500_8700.SplitData.node4652 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4653
  · rfl

def B4630 : Block := .branch 132 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4631, (.leaf 5 (Common.fact 329).pointIds 329), B4652]
theorem treeEq4630 : B4630.tree = HexagonCover.NBand.M8500_8700.SplitData.node4630 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4631
  · rfl
  · exact treeEq4652

def B4662 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq4662 : B4662.tree = HexagonCover.NBand.M8500_8700.SplitData.node4662 := by
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

def B4661 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4662, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq4661 : B4661.tree = HexagonCover.NBand.M8500_8700.SplitData.node4661 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4662
  · rfl

def B4660 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B4661]
theorem treeEq4660 : B4660.tree = HexagonCover.NBand.M8500_8700.SplitData.node4660 := by
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
  · exact treeEq4661

def B4659 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B4660, (.leaf 0 [] 0)]
theorem treeEq4659 : B4659.tree = HexagonCover.NBand.M8500_8700.SplitData.node4659 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4660
  · rfl

def B4658 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B4659, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq4658 : B4658.tree = HexagonCover.NBand.M8500_8700.SplitData.node4658 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4659
  · rfl

def B4629 : Block := .branch 129 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B4630, B4658, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq4629 : B4629.tree = HexagonCover.NBand.M8500_8700.SplitData.node4629 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4630
  · exact treeEq4658
  · rfl
  · rfl

theorem accepted4629 : B4629.accepted = true := by decide +kernel
theorem checked4629 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4629 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq4629]
  exact B4629.sound accepted4629
#print axioms checked4629

def B4691 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq4691 : B4691.tree = HexagonCover.NBand.M8500_8700.SplitData.node4691 := by
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

def B4690 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4691, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq4690 : B4690.tree = HexagonCover.NBand.M8500_8700.SplitData.node4690 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4691
  · rfl

def B4689 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4690]
theorem treeEq4689 : B4689.tree = HexagonCover.NBand.M8500_8700.SplitData.node4689 := by
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
  · exact treeEq4690

def B4688 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4689, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq4688 : B4688.tree = HexagonCover.NBand.M8500_8700.SplitData.node4688 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4689
  · rfl
  · rfl
  · rfl

def B4687 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B4688]
theorem treeEq4687 : B4687.tree = HexagonCover.NBand.M8500_8700.SplitData.node4687 := by
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
  · exact treeEq4688

def B4693 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq4693 : B4693.tree = HexagonCover.NBand.M8500_8700.SplitData.node4693 := by
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

def B4692 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4693, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq4692 : B4692.tree = HexagonCover.NBand.M8500_8700.SplitData.node4692 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4693
  · rfl
  · rfl
  · rfl

def B4686 : Block := .branch 144 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B4687, B4692]
theorem treeEq4686 : B4686.tree = HexagonCover.NBand.M8500_8700.SplitData.node4686 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4687
  · exact treeEq4692

def B4699 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq4699 : B4699.tree = HexagonCover.NBand.M8500_8700.SplitData.node4699 := by
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

def B4698 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4699, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq4698 : B4698.tree = HexagonCover.NBand.M8500_8700.SplitData.node4698 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4699
  · rfl

def B4697 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4698]
theorem treeEq4697 : B4697.tree = HexagonCover.NBand.M8500_8700.SplitData.node4697 := by
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
  · exact treeEq4698

def B4696 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4697, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq4696 : B4696.tree = HexagonCover.NBand.M8500_8700.SplitData.node4696 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4697
  · rfl
  · rfl
  · rfl

def B4695 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B4696]
theorem treeEq4695 : B4695.tree = HexagonCover.NBand.M8500_8700.SplitData.node4695 := by
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
  · exact treeEq4696

def B4694 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B4695, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq4694 : B4694.tree = HexagonCover.NBand.M8500_8700.SplitData.node4694 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4695
  · rfl

def B4685 : Block := .branch 142 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B4686, (.leaf 5 (Common.fact 339).pointIds 339), B4694]
theorem treeEq4685 : B4685.tree = HexagonCover.NBand.M8500_8700.SplitData.node4685 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4686
  · rfl
  · exact treeEq4694

theorem accepted4685 : B4685.accepted = true := by decide +kernel
theorem checked4685 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4685 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq4685]
  exact B4685.sound accepted4685
#print axioms checked4685

def Tip4682_4685 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node4685 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] checked4685
def B4704 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4704 : B4704.tree = HexagonCover.NBand.M8500_8700.SplitData.node4704 := by
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

def B4703 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4704, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq4703 : B4703.tree = HexagonCover.NBand.M8500_8700.SplitData.node4703 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4704
  · rfl

def B4702 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B4703]
theorem treeEq4702 : B4702.tree = HexagonCover.NBand.M8500_8700.SplitData.node4702 := by
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
  · exact treeEq4703

def B4701 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B4702, (.leaf 0 [] 0)]
theorem treeEq4701 : B4701.tree = HexagonCover.NBand.M8500_8700.SplitData.node4701 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4702
  · rfl

def B4700 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B4701, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq4700 : B4700.tree = HexagonCover.NBand.M8500_8700.SplitData.node4700 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4701
  · rfl

def B4684 : Block := .branch 138 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip4682_4685, B4700, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq4684 : B4684.tree = HexagonCover.NBand.M8500_8700.SplitData.node4684 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4700
  · rfl
  · rfl

def B4710 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq4710 : B4710.tree = HexagonCover.NBand.M8500_8700.SplitData.node4710 := by
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

def B4709 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4710, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq4709 : B4709.tree = HexagonCover.NBand.M8500_8700.SplitData.node4709 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4710
  · rfl

def B4708 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4709]
theorem treeEq4708 : B4708.tree = HexagonCover.NBand.M8500_8700.SplitData.node4708 := by
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
  · exact treeEq4709

def B4707 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4708, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq4707 : B4707.tree = HexagonCover.NBand.M8500_8700.SplitData.node4707 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4708
  · rfl
  · rfl
  · rfl

def B4706 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B4707]
theorem treeEq4706 : B4706.tree = HexagonCover.NBand.M8500_8700.SplitData.node4706 := by
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
  · exact treeEq4707

def B4705 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B4706, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq4705 : B4705.tree = HexagonCover.NBand.M8500_8700.SplitData.node4705 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4706
  · rfl

def B4683 : Block := .branch 132 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4684, (.leaf 5 (Common.fact 329).pointIds 329), B4705]
theorem treeEq4683 : B4683.tree = HexagonCover.NBand.M8500_8700.SplitData.node4683 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4684
  · rfl
  · exact treeEq4705

def B4715 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4715 : B4715.tree = HexagonCover.NBand.M8500_8700.SplitData.node4715 := by
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

def B4714 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4715, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq4714 : B4714.tree = HexagonCover.NBand.M8500_8700.SplitData.node4714 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4715
  · rfl

def B4713 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B4714]
theorem treeEq4713 : B4713.tree = HexagonCover.NBand.M8500_8700.SplitData.node4713 := by
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
  · exact treeEq4714

def B4712 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B4713, (.leaf 0 [] 0)]
theorem treeEq4712 : B4712.tree = HexagonCover.NBand.M8500_8700.SplitData.node4712 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4713
  · rfl

def B4711 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B4712, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq4711 : B4711.tree = HexagonCover.NBand.M8500_8700.SplitData.node4711 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4712
  · rfl

def B4682 : Block := .branch 129 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B4683, B4711, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq4682 : B4682.tree = HexagonCover.NBand.M8500_8700.SplitData.node4682 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4683
  · exact treeEq4711
  · rfl
  · rfl

theorem accepted4682 : B4682.accepted = true := by decide +kernel
theorem checked4682 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4682 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq4682]
  exact B4682.sound accepted4682
#print axioms checked4682

end HexagonCover.NBand.M8500_8700.SplitTree.Run0064
