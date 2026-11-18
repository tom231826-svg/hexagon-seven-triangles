import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0052
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0053
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip3822_3825 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3825 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] HexagonCover.NBand.M8500_8700.SplitTree.Run0052.checked3825
def B3844 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq3844 : B3844.tree = HexagonCover.NBand.M8500_8700.SplitData.node3844 := by
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

def B3843 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3844, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq3843 : B3843.tree = HexagonCover.NBand.M8500_8700.SplitData.node3843 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3844
  · rfl

def B3842 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B3843]
theorem treeEq3842 : B3842.tree = HexagonCover.NBand.M8500_8700.SplitData.node3842 := by
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
  · exact treeEq3843

def B3841 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B3842, (.leaf 0 [] 0)]
theorem treeEq3841 : B3841.tree = HexagonCover.NBand.M8500_8700.SplitData.node3841 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3842
  · rfl

def B3840 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B3841, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3840 : B3840.tree = HexagonCover.NBand.M8500_8700.SplitData.node3840 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3841
  · rfl

def B3824 : Block := .branch 138 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip3822_3825, B3840, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq3824 : B3824.tree = HexagonCover.NBand.M8500_8700.SplitData.node3824 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3840
  · rfl
  · rfl

def B3850 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq3850 : B3850.tree = HexagonCover.NBand.M8500_8700.SplitData.node3850 := by
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

def B3849 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3850, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq3849 : B3849.tree = HexagonCover.NBand.M8500_8700.SplitData.node3849 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3850
  · rfl

def B3848 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3849]
theorem treeEq3848 : B3848.tree = HexagonCover.NBand.M8500_8700.SplitData.node3848 := by
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
  · exact treeEq3849

def B3847 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3848, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq3847 : B3847.tree = HexagonCover.NBand.M8500_8700.SplitData.node3847 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3848
  · rfl
  · rfl
  · rfl

def B3846 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B3847]
theorem treeEq3846 : B3846.tree = HexagonCover.NBand.M8500_8700.SplitData.node3846 := by
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
  · exact treeEq3847

def B3845 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415800590088685349345630151330430976064] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B3846, (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq3845 : B3845.tree = HexagonCover.NBand.M8500_8700.SplitData.node3845 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3846
  · rfl

def B3823 : Block := .branch 132 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B3824, (.leaf 5 (Common.fact 329).pointIds 329), B3845]
theorem treeEq3823 : B3823.tree = HexagonCover.NBand.M8500_8700.SplitData.node3823 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3824
  · rfl
  · exact treeEq3845

def B3855 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq3855 : B3855.tree = HexagonCover.NBand.M8500_8700.SplitData.node3855 := by
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

def B3854 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3855, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq3854 : B3854.tree = HexagonCover.NBand.M8500_8700.SplitData.node3854 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3855
  · rfl

def B3853 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B3854]
theorem treeEq3853 : B3853.tree = HexagonCover.NBand.M8500_8700.SplitData.node3853 := by
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
  · exact treeEq3854

def B3852 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B3853, (.leaf 0 [] 0)]
theorem treeEq3852 : B3852.tree = HexagonCover.NBand.M8500_8700.SplitData.node3852 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3853
  · rfl

def B3851 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B3852, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3851 : B3851.tree = HexagonCover.NBand.M8500_8700.SplitData.node3851 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3852
  · rfl

def B3822 : Block := .branch 129 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B3823, B3851, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq3822 : B3822.tree = HexagonCover.NBand.M8500_8700.SplitData.node3822 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3823
  · exact treeEq3851
  · rfl
  · rfl

theorem accepted3822 : B3822.accepted = true := by decide +kernel
theorem checked3822 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3822 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq3822]
  exact B3822.sound accepted3822
#print axioms checked3822

def Tip3765_3769 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3769 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0052.checked3769
def B3806 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3806 : B3806.tree = HexagonCover.NBand.M8500_8700.SplitData.node3806 := by
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

def B3805 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3806, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq3805 : B3805.tree = HexagonCover.NBand.M8500_8700.SplitData.node3805 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3806
  · rfl
  · rfl
  · rfl

def B3804 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3805]
theorem treeEq3804 : B3804.tree = HexagonCover.NBand.M8500_8700.SplitData.node3804 := by
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
  · exact treeEq3805

def B3803 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973935983048381230849815516046371061824] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3804, (.leaf 6 (Common.fact 643).pointIds 643)]
theorem treeEq3803 : B3803.tree = HexagonCover.NBand.M8500_8700.SplitData.node3803 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3804
  · rfl

def B3768 : Block := .branch 121 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip3765_3769, (.leaf 5 (Common.fact 319).pointIds 319), B3803]
theorem treeEq3768 : B3768.tree = HexagonCover.NBand.M8500_8700.SplitData.node3768 := by
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
  · exact treeEq3803

def B3811 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq3811 : B3811.tree = HexagonCover.NBand.M8500_8700.SplitData.node3811 := by
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

def B3810 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3811, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq3810 : B3810.tree = HexagonCover.NBand.M8500_8700.SplitData.node3810 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3811
  · rfl

def B3809 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B3810]
theorem treeEq3809 : B3809.tree = HexagonCover.NBand.M8500_8700.SplitData.node3809 := by
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
  · exact treeEq3810

def B3808 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B3809, (.leaf 0 [] 0)]
theorem treeEq3808 : B3808.tree = HexagonCover.NBand.M8500_8700.SplitData.node3808 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3809
  · rfl

def B3807 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B3808, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3807 : B3807.tree = HexagonCover.NBand.M8500_8700.SplitData.node3807 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3808
  · rfl

def B3767 : Block := .branch 119 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B3768, B3807, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq3767 : B3767.tree = HexagonCover.NBand.M8500_8700.SplitData.node3767 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3768
  · exact treeEq3807
  · rfl
  · rfl

def B3813 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq3813 : B3813.tree = HexagonCover.NBand.M8500_8700.SplitData.node3813 := by
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

def B3812 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3813, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq3812 : B3812.tree = HexagonCover.NBand.M8500_8700.SplitData.node3812 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3813
  · rfl
  · rfl
  · rfl

def B3766 : Block := .branch 114 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B3767, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B3812]
theorem treeEq3766 : B3766.tree = HexagonCover.NBand.M8500_8700.SplitData.node3766 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3767
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3812

def B3817 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq3817 : B3817.tree = HexagonCover.NBand.M8500_8700.SplitData.node3817 := by
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

def B3816 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3817, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq3816 : B3816.tree = HexagonCover.NBand.M8500_8700.SplitData.node3816 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3817
  · rfl

def B3815 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3816]
theorem treeEq3815 : B3815.tree = HexagonCover.NBand.M8500_8700.SplitData.node3815 := by
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
  · exact treeEq3816

def B3814 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3815, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq3814 : B3814.tree = HexagonCover.NBand.M8500_8700.SplitData.node3814 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3815
  · rfl
  · rfl
  · rfl

def B3765 : Block := .branch 113 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![B3766, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B3814]
theorem treeEq3765 : B3765.tree = HexagonCover.NBand.M8500_8700.SplitData.node3765 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3766
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3814

theorem accepted3765 : B3765.accepted = true := by decide +kernel
theorem checked3765 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3765 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3765]
  exact B3765.sound accepted3765
#print axioms checked3765

def Tip3764_3822 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3822 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638389943763762426415598745871887892544] checked3822
def Tip3764_3765 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3765 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked3765
def B3859 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507379017576607879913888757764604012027912, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 636).pointIds 636), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3859 : B3859.tree = HexagonCover.NBand.M8500_8700.SplitData.node3859 := by
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

def B3858 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614314805107993509253904315998216, 1329227995784915872903807060280442896, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3859, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq3858 : B3858.tree = HexagonCover.NBand.M8500_8700.SplitData.node3858 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3859
  · rfl
  · rfl
  · rfl

def B3857 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193931400687183263922916893690117400035392] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3858]
theorem treeEq3857 : B3857.tree = HexagonCover.NBand.M8500_8700.SplitData.node3857 := by
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
  · exact treeEq3858

def B3856 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1329227995784915872903807060280442896, 393248, 11193973941175345239765677444046542700281920] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3857, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq3856 : B3856.tree = HexagonCover.NBand.M8500_8700.SplitData.node3856 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3857
  · rfl

def B3821 : Block := .branch 121 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 664614473261433022037929091403898888, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), Tip3764_3822, (.leaf 5 (Common.fact 319).pointIds 319), B3856]
theorem treeEq3821 : B3821.tree = HexagonCover.NBand.M8500_8700.SplitData.node3821 := by
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
  · exact treeEq3856

def B3864 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq3864 : B3864.tree = HexagonCover.NBand.M8500_8700.SplitData.node3864 := by
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

def B3863 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3864, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq3863 : B3863.tree = HexagonCover.NBand.M8500_8700.SplitData.node3863 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3864
  · rfl

def B3862 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B3863]
theorem treeEq3862 : B3862.tree = HexagonCover.NBand.M8500_8700.SplitData.node3862 := by
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
  · exact treeEq3863

def B3861 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B3862, (.leaf 0 [] 0)]
theorem treeEq3861 : B3861.tree = HexagonCover.NBand.M8500_8700.SplitData.node3861 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3862
  · rfl

def B3860 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B3861, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3860 : B3860.tree = HexagonCover.NBand.M8500_8700.SplitData.node3860 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3861
  · rfl

def B3820 : Block := .branch 119 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B3821, B3860, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq3820 : B3820.tree = HexagonCover.NBand.M8500_8700.SplitData.node3820 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3821
  · exact treeEq3860
  · rfl
  · rfl

def B3866 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287128541114379032644229892431880, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq3866 : B3866.tree = HexagonCover.NBand.M8500_8700.SplitData.node3866 := by
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

def B3865 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324835466308483784133530196402184, 1329227995784915872903807060280442896, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3866, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq3865 : B3865.tree = HexagonCover.NBand.M8500_8700.SplitData.node3865 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3866
  · rfl
  · rfl
  · rfl

def B3819 : Block := .branch 114 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B3820, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B3865]
theorem treeEq3819 : B3819.tree = HexagonCover.NBand.M8500_8700.SplitData.node3819 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3820
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3865

def B3870 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq3870 : B3870.tree = HexagonCover.NBand.M8500_8700.SplitData.node3870 := by
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

def B3869 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3870, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq3869 : B3869.tree = HexagonCover.NBand.M8500_8700.SplitData.node3869 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3870
  · rfl

def B3868 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3869]
theorem treeEq3868 : B3868.tree = HexagonCover.NBand.M8500_8700.SplitData.node3868 := by
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
  · exact treeEq3869

def B3867 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3868, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq3867 : B3867.tree = HexagonCover.NBand.M8500_8700.SplitData.node3867 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3868
  · rfl
  · rfl
  · rfl

def B3818 : Block := .branch 113 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638389943763762426415598745871887892544] ![B3819, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B3867]
theorem treeEq3818 : B3818.tree = HexagonCover.NBand.M8500_8700.SplitData.node3818 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3819
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3867

def B3764 : Block := .branch 112 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![Tip3764_3765, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B3818]
theorem treeEq3764 : B3764.tree = HexagonCover.NBand.M8500_8700.SplitData.node3764 := by
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
  · exact treeEq3818

theorem accepted3764 : B3764.accepted = true := by decide +kernel
theorem checked3764 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3764 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3764]
  exact B3764.sound accepted3764
#print axioms checked3764

def Tip3760_3764 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3764 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 324993922633512312808717284302856, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] checked3764
def B3872 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq3872 : B3872.tree = HexagonCover.NBand.M8500_8700.SplitData.node3872 := by
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

def B3871 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3872, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq3871 : B3871.tree = HexagonCover.NBand.M8500_8700.SplitData.node3871 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3872
  · rfl

def B3763 : Block := .branch 109 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 325073150796026577146310828253192, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip3760_3764, (.leaf 5 (Common.fact 294).pointIds 294), B3871]
theorem treeEq3763 : B3763.tree = HexagonCover.NBand.M8500_8700.SplitData.node3763 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3871

def B3877 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq3877 : B3877.tree = HexagonCover.NBand.M8500_8700.SplitData.node3877 := by
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

def B3876 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3877, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq3876 : B3876.tree = HexagonCover.NBand.M8500_8700.SplitData.node3876 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3877
  · rfl

def B3875 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B3876]
theorem treeEq3875 : B3875.tree = HexagonCover.NBand.M8500_8700.SplitData.node3875 := by
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
  · exact treeEq3876

def B3874 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B3875, (.leaf 0 [] 0)]
theorem treeEq3874 : B3874.tree = HexagonCover.NBand.M8500_8700.SplitData.node3874 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3875
  · rfl

def B3873 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B3874, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3873 : B3873.tree = HexagonCover.NBand.M8500_8700.SplitData.node3873 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3874
  · rfl

def B3762 : Block := .branch 108 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B3763, B3873, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq3762 : B3762.tree = HexagonCover.NBand.M8500_8700.SplitData.node3762 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3763
  · exact treeEq3873
  · rfl
  · rfl

def B3879 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq3879 : B3879.tree = HexagonCover.NBand.M8500_8700.SplitData.node3879 := by
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

def B3878 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3879, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq3878 : B3878.tree = HexagonCover.NBand.M8500_8700.SplitData.node3878 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3879
  · rfl
  · rfl
  · rfl

def B3761 : Block := .branch 100 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 554597137599850363154807676936, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![B3762, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B3878]
theorem treeEq3761 : B3761.tree = HexagonCover.NBand.M8500_8700.SplitData.node3761 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3762
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3878

def B3884 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq3884 : B3884.tree = HexagonCover.NBand.M8500_8700.SplitData.node3884 := by
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

def B3883 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3884, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq3883 : B3883.tree = HexagonCover.NBand.M8500_8700.SplitData.node3883 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3884
  · rfl

def B3882 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B3883]
theorem treeEq3882 : B3882.tree = HexagonCover.NBand.M8500_8700.SplitData.node3882 := by
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
  · exact treeEq3883

def B3881 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B3882, (.leaf 0 [] 0)]
theorem treeEq3881 : B3881.tree = HexagonCover.NBand.M8500_8700.SplitData.node3881 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3882
  · rfl

def B3880 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B3881, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3880 : B3880.tree = HexagonCover.NBand.M8500_8700.SplitData.node3880 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3881
  · rfl

def B3760 : Block := .branch 98 ![1237940039287632074712809857, 151115727522747146831362, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B3761, B3880, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq3760 : B3760.tree = HexagonCover.NBand.M8500_8700.SplitData.node3760 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3761
  · exact treeEq3880
  · rfl
  · rfl

theorem accepted3760 : B3760.accepted = true := by decide +kernel
theorem checked3760 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3760 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3760]
  exact B3760.sound accepted3760
#print axioms checked3760

end HexagonCover.NBand.M8500_8700.SplitTree.Run0053
