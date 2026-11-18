import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0036
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0037
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip2681_2685 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2685 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] HexagonCover.NBand.M8500_8700.SplitTree.Run0036.checked2685
def B2704 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq2704 : B2704.tree = HexagonCover.NBand.M8500_8700.SplitData.node2704 := by
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

def B2703 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2704, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2703 : B2703.tree = HexagonCover.NBand.M8500_8700.SplitData.node2703 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2704
  · rfl

def B2702 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B2703]
theorem treeEq2702 : B2702.tree = HexagonCover.NBand.M8500_8700.SplitData.node2702 := by
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
  · exact treeEq2703

def B2701 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B2702, (.leaf 0 [] 0)]
theorem treeEq2701 : B2701.tree = HexagonCover.NBand.M8500_8700.SplitData.node2701 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2702
  · rfl

def B2700 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B2701, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2700 : B2700.tree = HexagonCover.NBand.M8500_8700.SplitData.node2700 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2701
  · rfl

def B2684 : Block := .branch 119 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip2681_2685, B2700, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq2684 : B2684.tree = HexagonCover.NBand.M8500_8700.SplitData.node2684 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2700
  · rfl
  · rfl

def B2707 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq2707 : B2707.tree = HexagonCover.NBand.M8500_8700.SplitData.node2707 := by
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

def B2706 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2707, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq2706 : B2706.tree = HexagonCover.NBand.M8500_8700.SplitData.node2706 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2707
  · rfl
  · rfl
  · rfl
  · rfl

def B2705 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2706, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2705 : B2705.tree = HexagonCover.NBand.M8500_8700.SplitData.node2705 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2706
  · rfl
  · rfl
  · rfl

def B2683 : Block := .branch 114 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B2684, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B2705]
theorem treeEq2683 : B2683.tree = HexagonCover.NBand.M8500_8700.SplitData.node2683 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2684
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2705

def B2712 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2712 : B2712.tree = HexagonCover.NBand.M8500_8700.SplitData.node2712 := by
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

def B2711 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2712, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2711 : B2711.tree = HexagonCover.NBand.M8500_8700.SplitData.node2711 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2712
  · rfl

def B2710 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2711]
theorem treeEq2710 : B2710.tree = HexagonCover.NBand.M8500_8700.SplitData.node2710 := by
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
  · exact treeEq2711

def B2709 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 851).pointIds 851), B2710, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq2709 : B2709.tree = HexagonCover.NBand.M8500_8700.SplitData.node2709 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2710
  · rfl
  · rfl
  · rfl

def B2708 : Block := .branch 160 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), B2709, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq2708 : B2708.tree = HexagonCover.NBand.M8500_8700.SplitData.node2708 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2709
  · rfl
  · rfl
  · rfl
  · rfl

def B2682 : Block := .branch 113 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B2683, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B2708]
theorem treeEq2682 : B2682.tree = HexagonCover.NBand.M8500_8700.SplitData.node2682 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2683
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2708

def B2681 : Block := .branch 159 ![5193565747377326600467725038911873, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 942).pointIds 942), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B2682]
theorem treeEq2681 : B2681.tree = HexagonCover.NBand.M8500_8700.SplitData.node2681 := by
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
  · exact treeEq2682

theorem accepted2681 : B2681.accepted = true := by decide +kernel
theorem checked2681 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2681 (maskNeeds ![5193565747377326600467725038911873, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2681]
  exact B2681.sound accepted2681
#print axioms checked2681

def Tip2680_2717 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2717 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] HexagonCover.NBand.M8500_8700.SplitTree.Run0036.checked2717
def Tip2680_2681 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2681 ![5193565747377326600467725038911873, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] checked2681
def B2736 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq2736 : B2736.tree = HexagonCover.NBand.M8500_8700.SplitData.node2736 := by
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

def B2735 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2736, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq2735 : B2735.tree = HexagonCover.NBand.M8500_8700.SplitData.node2735 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2736
  · rfl

def B2734 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B2735]
theorem treeEq2734 : B2734.tree = HexagonCover.NBand.M8500_8700.SplitData.node2734 := by
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
  · exact treeEq2735

def B2733 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B2734, (.leaf 0 [] 0)]
theorem treeEq2733 : B2733.tree = HexagonCover.NBand.M8500_8700.SplitData.node2733 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2734
  · rfl

def B2732 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B2733, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2732 : B2732.tree = HexagonCover.NBand.M8500_8700.SplitData.node2732 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2733
  · rfl

def B2716 : Block := .branch 119 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip2680_2717, B2732, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq2716 : B2716.tree = HexagonCover.NBand.M8500_8700.SplitData.node2716 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2732
  · rfl
  · rfl

def B2739 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq2739 : B2739.tree = HexagonCover.NBand.M8500_8700.SplitData.node2739 := by
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

def B2738 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2739, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2738 : B2738.tree = HexagonCover.NBand.M8500_8700.SplitData.node2738 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2739
  · rfl
  · rfl
  · rfl
  · rfl

def B2737 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2738, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2737 : B2737.tree = HexagonCover.NBand.M8500_8700.SplitData.node2737 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2738
  · rfl
  · rfl
  · rfl

def B2715 : Block := .branch 114 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![B2716, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B2737]
theorem treeEq2715 : B2715.tree = HexagonCover.NBand.M8500_8700.SplitData.node2715 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2716
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2737

def B2714 : Block := .branch 159 ![10385862605912154228998221368131969, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B2715]
theorem treeEq2714 : B2714.tree = HexagonCover.NBand.M8500_8700.SplitData.node2714 := by
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
  · exact treeEq2715

def B2744 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2744 : B2744.tree = HexagonCover.NBand.M8500_8700.SplitData.node2744 := by
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

def B2743 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2744, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2743 : B2743.tree = HexagonCover.NBand.M8500_8700.SplitData.node2743 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2744
  · rfl

def B2742 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2743]
theorem treeEq2742 : B2742.tree = HexagonCover.NBand.M8500_8700.SplitData.node2742 := by
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
  · exact treeEq2743

def B2741 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 851).pointIds 851), B2742, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2741 : B2741.tree = HexagonCover.NBand.M8500_8700.SplitData.node2741 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2742
  · rfl
  · rfl
  · rfl

def B2740 : Block := .branch 160 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), B2741, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq2740 : B2740.tree = HexagonCover.NBand.M8500_8700.SplitData.node2740 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2741
  · rfl
  · rfl
  · rfl
  · rfl

def B2713 : Block := .branch 113 ![1268888842498971937228709691777, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![B2714, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B2740]
theorem treeEq2713 : B2713.tree = HexagonCover.NBand.M8500_8700.SplitData.node2713 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2714
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2740

def B2680 : Block := .branch 112 ![1268888842498971937228709691777, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip2680_2681, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B2713]
theorem treeEq2680 : B2680.tree = HexagonCover.NBand.M8500_8700.SplitData.node2680 := by
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
  · exact treeEq2713

theorem accepted2680 : B2680.accepted = true := by decide +kernel
theorem checked2680 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2680 (maskNeeds ![1268888842498971937228709691777, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2680]
  exact B2680.sound accepted2680
#print axioms checked2680

def Tip2592_2596 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2596 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0036.checked2596
def B2662 : Block := .branch 168 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq2662 : B2662.tree = HexagonCover.NBand.M8500_8700.SplitData.node2662 := by
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

def B2661 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2662, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq2661 : B2661.tree = HexagonCover.NBand.M8500_8700.SplitData.node2661 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2662
  · rfl

def B2595 : Block := .branch 109 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 325073155631729855604827527077896, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip2592_2596, (.leaf 5 (Common.fact 294).pointIds 294), B2661]
theorem treeEq2595 : B2595.tree = HexagonCover.NBand.M8500_8700.SplitData.node2595 := by
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
  · exact treeEq2661

def B2667 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2667 : B2667.tree = HexagonCover.NBand.M8500_8700.SplitData.node2667 := by
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

def B2666 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2667, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2666 : B2666.tree = HexagonCover.NBand.M8500_8700.SplitData.node2666 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2667
  · rfl

def B2665 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B2666]
theorem treeEq2665 : B2665.tree = HexagonCover.NBand.M8500_8700.SplitData.node2665 := by
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
  · exact treeEq2666

def B2664 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B2665, (.leaf 0 [] 0)]
theorem treeEq2664 : B2664.tree = HexagonCover.NBand.M8500_8700.SplitData.node2664 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2665
  · rfl

def B2663 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B2664, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2663 : B2663.tree = HexagonCover.NBand.M8500_8700.SplitData.node2663 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2664
  · rfl

def B2594 : Block := .branch 108 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B2595, B2663, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq2594 : B2594.tree = HexagonCover.NBand.M8500_8700.SplitData.node2594 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2595
  · exact treeEq2663
  · rfl
  · rfl

def B2670 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq2670 : B2670.tree = HexagonCover.NBand.M8500_8700.SplitData.node2670 := by
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

def B2669 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2670, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq2669 : B2669.tree = HexagonCover.NBand.M8500_8700.SplitData.node2669 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2670
  · rfl
  · rfl
  · rfl
  · rfl

def B2668 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2669, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq2668 : B2668.tree = HexagonCover.NBand.M8500_8700.SplitData.node2668 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2669
  · rfl
  · rfl
  · rfl

def B2593 : Block := .branch 100 ![1856910058930322212162371969, 151116339941927725041154, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B2594, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B2668]
theorem treeEq2593 : B2593.tree = HexagonCover.NBand.M8500_8700.SplitData.node2593 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2594
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2668

def B2675 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2675 : B2675.tree = HexagonCover.NBand.M8500_8700.SplitData.node2675 := by
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

def B2674 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2675, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2674 : B2674.tree = HexagonCover.NBand.M8500_8700.SplitData.node2674 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2675
  · rfl

def B2673 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B2674]
theorem treeEq2673 : B2673.tree = HexagonCover.NBand.M8500_8700.SplitData.node2673 := by
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
  · exact treeEq2674

def B2672 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B2673, (.leaf 0 [] 0)]
theorem treeEq2672 : B2672.tree = HexagonCover.NBand.M8500_8700.SplitData.node2672 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2673
  · rfl

def B2671 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B2672, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2671 : B2671.tree = HexagonCover.NBand.M8500_8700.SplitData.node2671 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2672
  · rfl

def B2592 : Block := .branch 98 ![1856910058930322212162371969, 151116339941927725041154, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B2593, B2671, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq2592 : B2592.tree = HexagonCover.NBand.M8500_8700.SplitData.node2592 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2593
  · exact treeEq2671
  · rfl
  · rfl

theorem accepted2592 : B2592.accepted = true := by decide +kernel
theorem checked2592 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2592 (maskNeeds ![1856910058930322212162371969, 151116339941927725041154, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2592]
  exact B2592.sound accepted2592
#print axioms checked2592

def Tip2591_2680 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2680 ![1268888842498971937228709691777, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] checked2680
def Tip2591_2592 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2592 ![1856910058930322212162371969, 151116339941927725041154, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] checked2592
def B2746 : Block := .branch 168 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq2746 : B2746.tree = HexagonCover.NBand.M8500_8700.SplitData.node2746 := by
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

def B2745 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2746, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq2745 : B2745.tree = HexagonCover.NBand.M8500_8700.SplitData.node2745 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2746
  · rfl

def B2679 : Block := .branch 109 ![1268888842498971937228709691777, 151116339941927725041154, 9709185488779990559365124, 325073155631729855604827527077896, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip2591_2680, (.leaf 5 (Common.fact 294).pointIds 294), B2745]
theorem treeEq2679 : B2679.tree = HexagonCover.NBand.M8500_8700.SplitData.node2679 := by
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
  · exact treeEq2745

def B2751 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2751 : B2751.tree = HexagonCover.NBand.M8500_8700.SplitData.node2751 := by
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

def B2750 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2751, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2750 : B2750.tree = HexagonCover.NBand.M8500_8700.SplitData.node2750 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2751
  · rfl

def B2749 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B2750]
theorem treeEq2749 : B2749.tree = HexagonCover.NBand.M8500_8700.SplitData.node2749 := by
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
  · exact treeEq2750

def B2748 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B2749, (.leaf 0 [] 0)]
theorem treeEq2748 : B2748.tree = HexagonCover.NBand.M8500_8700.SplitData.node2748 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2749
  · rfl

def B2747 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B2748, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2747 : B2747.tree = HexagonCover.NBand.M8500_8700.SplitData.node2747 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2748
  · rfl

def B2678 : Block := .branch 108 ![1268888842498971937228709691777, 151116339941927725041154, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B2679, B2747, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq2678 : B2678.tree = HexagonCover.NBand.M8500_8700.SplitData.node2678 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2679
  · exact treeEq2747
  · rfl
  · rfl

def B2754 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq2754 : B2754.tree = HexagonCover.NBand.M8500_8700.SplitData.node2754 := by
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

def B2753 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2754, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq2753 : B2753.tree = HexagonCover.NBand.M8500_8700.SplitData.node2753 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2754
  · rfl
  · rfl
  · rfl
  · rfl

def B2752 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2753, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq2752 : B2752.tree = HexagonCover.NBand.M8500_8700.SplitData.node2752 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2753
  · rfl
  · rfl
  · rfl

def B2677 : Block := .branch 100 ![1238242270742535732006486401, 151116339941927725041154, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B2678, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B2752]
theorem treeEq2677 : B2677.tree = HexagonCover.NBand.M8500_8700.SplitData.node2677 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2678
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2752

def B2759 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2759 : B2759.tree = HexagonCover.NBand.M8500_8700.SplitData.node2759 := by
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

def B2758 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2759, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2758 : B2758.tree = HexagonCover.NBand.M8500_8700.SplitData.node2758 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2759
  · rfl

def B2757 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B2758]
theorem treeEq2757 : B2757.tree = HexagonCover.NBand.M8500_8700.SplitData.node2757 := by
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
  · exact treeEq2758

def B2756 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B2757, (.leaf 0 [] 0)]
theorem treeEq2756 : B2756.tree = HexagonCover.NBand.M8500_8700.SplitData.node2756 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2757
  · rfl

def B2755 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B2756, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2755 : B2755.tree = HexagonCover.NBand.M8500_8700.SplitData.node2755 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2756
  · rfl

def B2676 : Block := .branch 98 ![1238242270742535732006486401, 151116339941927725041154, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B2677, B2755, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq2676 : B2676.tree = HexagonCover.NBand.M8500_8700.SplitData.node2676 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2677
  · exact treeEq2755
  · rfl
  · rfl

def B2591 : Block := .branch 89 ![1238242270742535732006486401, 151116339941927725041154, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![Tip2591_2592, B2676, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq2591 : B2591.tree = HexagonCover.NBand.M8500_8700.SplitData.node2591 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2676
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2591 : B2591.accepted = true := by decide +kernel
theorem checked2591 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2591 (maskNeeds ![1238242270742535732006486401, 151116339941927725041154, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2591]
  exact B2591.sound accepted2591
#print axioms checked2591

end HexagonCover.NBand.M8500_8700.SplitTree.Run0037
