import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0050
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0051
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B3702 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq3702 : B3702.tree = HexagonCover.NBand.M8500_8700.SplitData.node3702 := by
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

def B3701 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3702, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq3701 : B3701.tree = HexagonCover.NBand.M8500_8700.SplitData.node3701 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3702
  · rfl

def B3700 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3701]
theorem treeEq3700 : B3700.tree = HexagonCover.NBand.M8500_8700.SplitData.node3700 := by
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
  · exact treeEq3701

def B3699 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3700, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq3699 : B3699.tree = HexagonCover.NBand.M8500_8700.SplitData.node3699 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3700
  · rfl
  · rfl
  · rfl

def B3698 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B3699]
theorem treeEq3698 : B3698.tree = HexagonCover.NBand.M8500_8700.SplitData.node3698 := by
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
  · exact treeEq3699

def B3704 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq3704 : B3704.tree = HexagonCover.NBand.M8500_8700.SplitData.node3704 := by
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

def B3703 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3704, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq3703 : B3703.tree = HexagonCover.NBand.M8500_8700.SplitData.node3703 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3704
  · rfl
  · rfl
  · rfl

def B3697 : Block := .branch 144 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B3698, B3703]
theorem treeEq3697 : B3697.tree = HexagonCover.NBand.M8500_8700.SplitData.node3697 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3698
  · exact treeEq3703

def B3710 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq3710 : B3710.tree = HexagonCover.NBand.M8500_8700.SplitData.node3710 := by
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

def B3709 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3710, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq3709 : B3709.tree = HexagonCover.NBand.M8500_8700.SplitData.node3709 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3710
  · rfl

def B3708 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3709]
theorem treeEq3708 : B3708.tree = HexagonCover.NBand.M8500_8700.SplitData.node3708 := by
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
  · exact treeEq3709

def B3707 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3708, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq3707 : B3707.tree = HexagonCover.NBand.M8500_8700.SplitData.node3707 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3708
  · rfl
  · rfl
  · rfl

def B3706 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B3707]
theorem treeEq3706 : B3706.tree = HexagonCover.NBand.M8500_8700.SplitData.node3706 := by
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
  · exact treeEq3707

def B3705 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B3706, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq3705 : B3705.tree = HexagonCover.NBand.M8500_8700.SplitData.node3705 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3706
  · rfl

def B3696 : Block := .branch 142 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B3697, (.leaf 5 (Common.fact 339).pointIds 339), B3705]
theorem treeEq3696 : B3696.tree = HexagonCover.NBand.M8500_8700.SplitData.node3696 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3697
  · rfl
  · exact treeEq3705

theorem accepted3696 : B3696.accepted = true := by decide +kernel
theorem checked3696 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3696 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq3696]
  exact B3696.sound accepted3696
#print axioms checked3696

def Tip3693_3696 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3696 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] checked3696
def B3715 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq3715 : B3715.tree = HexagonCover.NBand.M8500_8700.SplitData.node3715 := by
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

def B3714 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3715, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq3714 : B3714.tree = HexagonCover.NBand.M8500_8700.SplitData.node3714 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3715
  · rfl

def B3713 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B3714]
theorem treeEq3713 : B3713.tree = HexagonCover.NBand.M8500_8700.SplitData.node3713 := by
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
  · exact treeEq3714

def B3712 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B3713, (.leaf 0 [] 0)]
theorem treeEq3712 : B3712.tree = HexagonCover.NBand.M8500_8700.SplitData.node3712 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3713
  · rfl

def B3711 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B3712, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3711 : B3711.tree = HexagonCover.NBand.M8500_8700.SplitData.node3711 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3712
  · rfl

def B3695 : Block := .branch 138 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip3693_3696, B3711, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq3695 : B3695.tree = HexagonCover.NBand.M8500_8700.SplitData.node3695 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3711
  · rfl
  · rfl

def B3721 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq3721 : B3721.tree = HexagonCover.NBand.M8500_8700.SplitData.node3721 := by
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

def B3720 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3721, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq3720 : B3720.tree = HexagonCover.NBand.M8500_8700.SplitData.node3720 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3721
  · rfl

def B3719 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3720]
theorem treeEq3719 : B3719.tree = HexagonCover.NBand.M8500_8700.SplitData.node3719 := by
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
  · exact treeEq3720

def B3718 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3719, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq3718 : B3718.tree = HexagonCover.NBand.M8500_8700.SplitData.node3718 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3719
  · rfl
  · rfl
  · rfl

def B3717 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B3718]
theorem treeEq3717 : B3717.tree = HexagonCover.NBand.M8500_8700.SplitData.node3717 := by
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
  · exact treeEq3718

def B3716 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B3717, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq3716 : B3716.tree = HexagonCover.NBand.M8500_8700.SplitData.node3716 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3717
  · rfl

def B3694 : Block := .branch 132 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B3695, (.leaf 5 (Common.fact 329).pointIds 329), B3716]
theorem treeEq3694 : B3694.tree = HexagonCover.NBand.M8500_8700.SplitData.node3694 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3695
  · rfl
  · exact treeEq3716

def B3726 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq3726 : B3726.tree = HexagonCover.NBand.M8500_8700.SplitData.node3726 := by
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

def B3725 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3726, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq3725 : B3725.tree = HexagonCover.NBand.M8500_8700.SplitData.node3725 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3726
  · rfl

def B3724 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B3725]
theorem treeEq3724 : B3724.tree = HexagonCover.NBand.M8500_8700.SplitData.node3724 := by
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
  · exact treeEq3725

def B3723 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B3724, (.leaf 0 [] 0)]
theorem treeEq3723 : B3723.tree = HexagonCover.NBand.M8500_8700.SplitData.node3723 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3724
  · rfl

def B3722 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B3723, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3722 : B3722.tree = HexagonCover.NBand.M8500_8700.SplitData.node3722 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3723
  · rfl

def B3693 : Block := .branch 129 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B3694, B3722, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq3693 : B3693.tree = HexagonCover.NBand.M8500_8700.SplitData.node3693 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3694
  · exact treeEq3722
  · rfl
  · rfl

theorem accepted3693 : B3693.accepted = true := by decide +kernel
theorem checked3693 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3693 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq3693]
  exact B3693.sound accepted3693
#print axioms checked3693

def Tip3636_3640 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3640 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0050.checked3640
def B3677 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3677 : B3677.tree = HexagonCover.NBand.M8500_8700.SplitData.node3677 := by
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

def B3676 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3677, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq3676 : B3676.tree = HexagonCover.NBand.M8500_8700.SplitData.node3676 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3677
  · rfl
  · rfl
  · rfl

def B3675 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3676]
theorem treeEq3675 : B3675.tree = HexagonCover.NBand.M8500_8700.SplitData.node3675 := by
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
  · exact treeEq3676

def B3674 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3675, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq3674 : B3674.tree = HexagonCover.NBand.M8500_8700.SplitData.node3674 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3675
  · rfl

def B3639 : Block := .branch 121 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip3636_3640, (.leaf 5 (Common.fact 319).pointIds 319), B3674]
theorem treeEq3639 : B3639.tree = HexagonCover.NBand.M8500_8700.SplitData.node3639 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3674

def B3682 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq3682 : B3682.tree = HexagonCover.NBand.M8500_8700.SplitData.node3682 := by
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

def B3681 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3682, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq3681 : B3681.tree = HexagonCover.NBand.M8500_8700.SplitData.node3681 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3682
  · rfl

def B3680 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B3681]
theorem treeEq3680 : B3680.tree = HexagonCover.NBand.M8500_8700.SplitData.node3680 := by
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
  · exact treeEq3681

def B3679 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B3680, (.leaf 0 [] 0)]
theorem treeEq3679 : B3679.tree = HexagonCover.NBand.M8500_8700.SplitData.node3679 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3680
  · rfl

def B3678 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B3679, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3678 : B3678.tree = HexagonCover.NBand.M8500_8700.SplitData.node3678 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3679
  · rfl

def B3638 : Block := .branch 119 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B3639, B3678, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq3638 : B3638.tree = HexagonCover.NBand.M8500_8700.SplitData.node3638 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3639
  · exact treeEq3678
  · rfl
  · rfl

def B3684 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq3684 : B3684.tree = HexagonCover.NBand.M8500_8700.SplitData.node3684 := by
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

def B3683 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3684, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq3683 : B3683.tree = HexagonCover.NBand.M8500_8700.SplitData.node3683 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3684
  · rfl
  · rfl
  · rfl

def B3637 : Block := .branch 114 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B3638, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B3683]
theorem treeEq3637 : B3637.tree = HexagonCover.NBand.M8500_8700.SplitData.node3637 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3638
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3683

def B3688 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq3688 : B3688.tree = HexagonCover.NBand.M8500_8700.SplitData.node3688 := by
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

def B3687 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3688, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq3687 : B3687.tree = HexagonCover.NBand.M8500_8700.SplitData.node3687 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3688
  · rfl

def B3686 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3687]
theorem treeEq3686 : B3686.tree = HexagonCover.NBand.M8500_8700.SplitData.node3686 := by
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
  · exact treeEq3687

def B3685 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3686, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq3685 : B3685.tree = HexagonCover.NBand.M8500_8700.SplitData.node3685 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3686
  · rfl
  · rfl
  · rfl

def B3636 : Block := .branch 113 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B3637, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B3685]
theorem treeEq3636 : B3636.tree = HexagonCover.NBand.M8500_8700.SplitData.node3636 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3637
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3685

theorem accepted3636 : B3636.accepted = true := by decide +kernel
theorem checked3636 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3636 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3636]
  exact B3636.sound accepted3636
#print axioms checked3636

def Tip3635_3693 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3693 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] checked3693
def Tip3635_3636 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3636 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked3636
def B3730 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3730 : B3730.tree = HexagonCover.NBand.M8500_8700.SplitData.node3730 := by
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

def B3729 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3730, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq3729 : B3729.tree = HexagonCover.NBand.M8500_8700.SplitData.node3729 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3730
  · rfl
  · rfl
  · rfl

def B3728 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3729]
theorem treeEq3728 : B3728.tree = HexagonCover.NBand.M8500_8700.SplitData.node3728 := by
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
  · exact treeEq3729

def B3727 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3728, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq3727 : B3727.tree = HexagonCover.NBand.M8500_8700.SplitData.node3727 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3728
  · rfl

def B3692 : Block := .branch 121 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip3635_3693, (.leaf 5 (Common.fact 319).pointIds 319), B3727]
theorem treeEq3692 : B3692.tree = HexagonCover.NBand.M8500_8700.SplitData.node3692 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3727

def B3735 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq3735 : B3735.tree = HexagonCover.NBand.M8500_8700.SplitData.node3735 := by
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

def B3734 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3735, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq3734 : B3734.tree = HexagonCover.NBand.M8500_8700.SplitData.node3734 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3735
  · rfl

def B3733 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B3734]
theorem treeEq3733 : B3733.tree = HexagonCover.NBand.M8500_8700.SplitData.node3733 := by
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
  · exact treeEq3734

def B3732 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B3733, (.leaf 0 [] 0)]
theorem treeEq3732 : B3732.tree = HexagonCover.NBand.M8500_8700.SplitData.node3732 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3733
  · rfl

def B3731 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B3732, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3731 : B3731.tree = HexagonCover.NBand.M8500_8700.SplitData.node3731 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3732
  · rfl

def B3691 : Block := .branch 119 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B3692, B3731, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq3691 : B3691.tree = HexagonCover.NBand.M8500_8700.SplitData.node3691 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3692
  · exact treeEq3731
  · rfl
  · rfl

def B3737 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq3737 : B3737.tree = HexagonCover.NBand.M8500_8700.SplitData.node3737 := by
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

def B3736 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3737, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq3736 : B3736.tree = HexagonCover.NBand.M8500_8700.SplitData.node3736 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3737
  · rfl
  · rfl
  · rfl

def B3690 : Block := .branch 114 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B3691, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B3736]
theorem treeEq3690 : B3690.tree = HexagonCover.NBand.M8500_8700.SplitData.node3690 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3691
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3736

def B3741 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq3741 : B3741.tree = HexagonCover.NBand.M8500_8700.SplitData.node3741 := by
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

def B3740 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3741, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq3740 : B3740.tree = HexagonCover.NBand.M8500_8700.SplitData.node3740 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3741
  · rfl

def B3739 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3740]
theorem treeEq3739 : B3739.tree = HexagonCover.NBand.M8500_8700.SplitData.node3739 := by
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
  · exact treeEq3740

def B3738 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3739, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq3738 : B3738.tree = HexagonCover.NBand.M8500_8700.SplitData.node3738 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3739
  · rfl
  · rfl
  · rfl

def B3689 : Block := .branch 113 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B3690, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B3738]
theorem treeEq3689 : B3689.tree = HexagonCover.NBand.M8500_8700.SplitData.node3689 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3690
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3738

def B3635 : Block := .branch 112 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![Tip3635_3636, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B3689]
theorem treeEq3635 : B3635.tree = HexagonCover.NBand.M8500_8700.SplitData.node3635 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3689

theorem accepted3635 : B3635.accepted = true := by decide +kernel
theorem checked3635 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3635 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3635]
  exact B3635.sound accepted3635
#print axioms checked3635

end HexagonCover.NBand.M8500_8700.SplitTree.Run0051
