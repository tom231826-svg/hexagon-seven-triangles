import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0039
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0040
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip2874_2911 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2911 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] HexagonCover.NBand.M8500_8700.SplitTree.Run0039.checked2911
def Tip2874_2875 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2875 ![5192298715444886558852708491592065, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0039.checked2875
def B2930 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq2930 : B2930.tree = HexagonCover.NBand.M8500_8700.SplitData.node2930 := by
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

def B2929 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2930, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq2929 : B2929.tree = HexagonCover.NBand.M8500_8700.SplitData.node2929 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2930
  · rfl

def B2928 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B2929]
theorem treeEq2928 : B2928.tree = HexagonCover.NBand.M8500_8700.SplitData.node2928 := by
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
  · exact treeEq2929

def B2927 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B2928, (.leaf 0 [] 0)]
theorem treeEq2927 : B2927.tree = HexagonCover.NBand.M8500_8700.SplitData.node2927 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2928
  · rfl

def B2926 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B2927, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2926 : B2926.tree = HexagonCover.NBand.M8500_8700.SplitData.node2926 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2927
  · rfl

def B2910 : Block := .branch 119 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip2874_2911, B2926, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq2910 : B2910.tree = HexagonCover.NBand.M8500_8700.SplitData.node2910 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2926
  · rfl
  · rfl

def B2933 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq2933 : B2933.tree = HexagonCover.NBand.M8500_8700.SplitData.node2933 := by
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

def B2932 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2933, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2932 : B2932.tree = HexagonCover.NBand.M8500_8700.SplitData.node2932 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2933
  · rfl
  · rfl
  · rfl
  · rfl

def B2931 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2932, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2931 : B2931.tree = HexagonCover.NBand.M8500_8700.SplitData.node2931 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2932
  · rfl
  · rfl
  · rfl

def B2909 : Block := .branch 114 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![B2910, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B2931]
theorem treeEq2909 : B2909.tree = HexagonCover.NBand.M8500_8700.SplitData.node2909 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2910
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2931

def B2908 : Block := .branch 159 ![10385863224579942416784701524017537, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 939).pointIds 939), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B2909]
theorem treeEq2908 : B2908.tree = HexagonCover.NBand.M8500_8700.SplitData.node2908 := by
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
  · exact treeEq2909

def B2938 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2938 : B2938.tree = HexagonCover.NBand.M8500_8700.SplitData.node2938 := by
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

def B2937 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2938, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2937 : B2937.tree = HexagonCover.NBand.M8500_8700.SplitData.node2937 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2938
  · rfl

def B2936 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2937]
theorem treeEq2936 : B2936.tree = HexagonCover.NBand.M8500_8700.SplitData.node2936 := by
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
  · exact treeEq2937

def B2935 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 851).pointIds 851), B2936, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2935 : B2935.tree = HexagonCover.NBand.M8500_8700.SplitData.node2935 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2936
  · rfl
  · rfl
  · rfl

def B2934 : Block := .branch 160 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), B2935, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq2934 : B2934.tree = HexagonCover.NBand.M8500_8700.SplitData.node2934 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2935
  · rfl
  · rfl
  · rfl
  · rfl

def B2907 : Block := .branch 113 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![B2908, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B2934]
theorem treeEq2907 : B2907.tree = HexagonCover.NBand.M8500_8700.SplitData.node2907 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2908
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2934

def B2874 : Block := .branch 112 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip2874_2875, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B2907]
theorem treeEq2874 : B2874.tree = HexagonCover.NBand.M8500_8700.SplitData.node2874 := by
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
  · exact treeEq2907

theorem accepted2874 : B2874.accepted = true := by decide +kernel
theorem checked2874 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2874 (maskNeeds ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2874]
  exact B2874.sound accepted2874
#print axioms checked2874

def B2967 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq2967 : B2967.tree = HexagonCover.NBand.M8500_8700.SplitData.node2967 := by
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

def B2966 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2967, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2966 : B2966.tree = HexagonCover.NBand.M8500_8700.SplitData.node2966 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2967
  · rfl

def B2965 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2966]
theorem treeEq2965 : B2965.tree = HexagonCover.NBand.M8500_8700.SplitData.node2965 := by
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
  · exact treeEq2966

def B2972 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq2972 : B2972.tree = HexagonCover.NBand.M8500_8700.SplitData.node2972 := by
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

def B2971 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2972, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2971 : B2971.tree = HexagonCover.NBand.M8500_8700.SplitData.node2971 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2972
  · rfl

def B2970 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B2971]
theorem treeEq2970 : B2970.tree = HexagonCover.NBand.M8500_8700.SplitData.node2970 := by
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
  · exact treeEq2971

def B2969 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B2970, (.leaf 0 [] 0)]
theorem treeEq2969 : B2969.tree = HexagonCover.NBand.M8500_8700.SplitData.node2969 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2970
  · rfl

def B2968 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B2969, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2968 : B2968.tree = HexagonCover.NBand.M8500_8700.SplitData.node2968 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2969
  · rfl

def B2964 : Block := .branch 129 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B2965, B2968, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq2964 : B2964.tree = HexagonCover.NBand.M8500_8700.SplitData.node2964 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2965
  · exact treeEq2968
  · rfl
  · rfl

def B2977 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq2977 : B2977.tree = HexagonCover.NBand.M8500_8700.SplitData.node2977 := by
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

def B2976 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2977, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq2976 : B2976.tree = HexagonCover.NBand.M8500_8700.SplitData.node2976 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2977
  · rfl
  · rfl
  · rfl
  · rfl

def B2975 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2976, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq2975 : B2975.tree = HexagonCover.NBand.M8500_8700.SplitData.node2975 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2976
  · rfl
  · rfl
  · rfl

def B2974 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B2975]
theorem treeEq2974 : B2974.tree = HexagonCover.NBand.M8500_8700.SplitData.node2974 := by
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
  · exact treeEq2975

def B2973 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2974, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq2973 : B2973.tree = HexagonCover.NBand.M8500_8700.SplitData.node2973 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2974
  · rfl

def B2963 : Block := .branch 121 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B2964, (.leaf 5 (Common.fact 319).pointIds 319), B2973]
theorem treeEq2963 : B2963.tree = HexagonCover.NBand.M8500_8700.SplitData.node2963 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2964
  · rfl
  · exact treeEq2973

theorem accepted2963 : B2963.accepted = true := by decide +kernel
theorem checked2963 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2963 (maskNeeds ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq2963]
  exact B2963.sound accepted2963
#print axioms checked2963

def B2999 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq2999 : B2999.tree = HexagonCover.NBand.M8500_8700.SplitData.node2999 := by
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

def B2998 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2999, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq2998 : B2998.tree = HexagonCover.NBand.M8500_8700.SplitData.node2998 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2999
  · rfl

def B2997 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2998]
theorem treeEq2997 : B2997.tree = HexagonCover.NBand.M8500_8700.SplitData.node2997 := by
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
  · exact treeEq2998

def B3004 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq3004 : B3004.tree = HexagonCover.NBand.M8500_8700.SplitData.node3004 := by
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

def B3003 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3004, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq3003 : B3003.tree = HexagonCover.NBand.M8500_8700.SplitData.node3003 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3004
  · rfl

def B3002 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B3003]
theorem treeEq3002 : B3002.tree = HexagonCover.NBand.M8500_8700.SplitData.node3002 := by
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
  · exact treeEq3003

def B3001 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B3002, (.leaf 0 [] 0)]
theorem treeEq3001 : B3001.tree = HexagonCover.NBand.M8500_8700.SplitData.node3001 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3002
  · rfl

def B3000 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B3001, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3000 : B3000.tree = HexagonCover.NBand.M8500_8700.SplitData.node3000 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3001
  · rfl

def B2996 : Block := .branch 129 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B2997, B3000, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq2996 : B2996.tree = HexagonCover.NBand.M8500_8700.SplitData.node2996 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2997
  · exact treeEq3000
  · rfl
  · rfl

def B3009 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq3009 : B3009.tree = HexagonCover.NBand.M8500_8700.SplitData.node3009 := by
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

def B3008 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B3009, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq3008 : B3008.tree = HexagonCover.NBand.M8500_8700.SplitData.node3008 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3009
  · rfl
  · rfl
  · rfl
  · rfl

def B3007 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B3008, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3007 : B3007.tree = HexagonCover.NBand.M8500_8700.SplitData.node3007 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3008
  · rfl
  · rfl
  · rfl

def B3006 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3007]
theorem treeEq3006 : B3006.tree = HexagonCover.NBand.M8500_8700.SplitData.node3006 := by
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
  · exact treeEq3007

def B3005 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3006, (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq3005 : B3005.tree = HexagonCover.NBand.M8500_8700.SplitData.node3005 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3006
  · rfl

def B2995 : Block := .branch 121 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B2996, (.leaf 5 (Common.fact 319).pointIds 319), B3005]
theorem treeEq2995 : B2995.tree = HexagonCover.NBand.M8500_8700.SplitData.node2995 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2996
  · rfl
  · exact treeEq3005

theorem accepted2995 : B2995.accepted = true := by decide +kernel
theorem checked2995 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2995 (maskNeeds ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032]) := by
  rw [← treeEq2995]
  exact B2995.sound accepted2995
#print axioms checked2995

def Tip2959_2963 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2963 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] checked2963
def B2982 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq2982 : B2982.tree = HexagonCover.NBand.M8500_8700.SplitData.node2982 := by
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

def B2981 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2982, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2981 : B2981.tree = HexagonCover.NBand.M8500_8700.SplitData.node2981 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2982
  · rfl

def B2980 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B2981]
theorem treeEq2980 : B2980.tree = HexagonCover.NBand.M8500_8700.SplitData.node2980 := by
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
  · exact treeEq2981

def B2979 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B2980, (.leaf 0 [] 0)]
theorem treeEq2979 : B2979.tree = HexagonCover.NBand.M8500_8700.SplitData.node2979 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2980
  · rfl

def B2978 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B2979, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2978 : B2978.tree = HexagonCover.NBand.M8500_8700.SplitData.node2978 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2979
  · rfl

def B2962 : Block := .branch 119 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip2959_2963, B2978, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq2962 : B2962.tree = HexagonCover.NBand.M8500_8700.SplitData.node2962 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2978
  · rfl
  · rfl

def B2985 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq2985 : B2985.tree = HexagonCover.NBand.M8500_8700.SplitData.node2985 := by
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

def B2984 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B2985, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq2984 : B2984.tree = HexagonCover.NBand.M8500_8700.SplitData.node2984 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2985
  · rfl
  · rfl
  · rfl
  · rfl

def B2983 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B2984, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2983 : B2983.tree = HexagonCover.NBand.M8500_8700.SplitData.node2983 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2984
  · rfl
  · rfl
  · rfl

def B2961 : Block := .branch 114 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B2962, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B2983]
theorem treeEq2961 : B2961.tree = HexagonCover.NBand.M8500_8700.SplitData.node2961 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2962
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2983

def B2990 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2990 : B2990.tree = HexagonCover.NBand.M8500_8700.SplitData.node2990 := by
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

def B2989 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2990, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2989 : B2989.tree = HexagonCover.NBand.M8500_8700.SplitData.node2989 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2990
  · rfl

def B2988 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2989]
theorem treeEq2988 : B2988.tree = HexagonCover.NBand.M8500_8700.SplitData.node2988 := by
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
  · exact treeEq2989

def B2987 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 851).pointIds 851), B2988, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq2987 : B2987.tree = HexagonCover.NBand.M8500_8700.SplitData.node2987 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2988
  · rfl
  · rfl
  · rfl

def B2986 : Block := .branch 160 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), B2987, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq2986 : B2986.tree = HexagonCover.NBand.M8500_8700.SplitData.node2986 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2987
  · rfl
  · rfl
  · rfl
  · rfl

def B2960 : Block := .branch 113 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B2961, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B2986]
theorem treeEq2960 : B2960.tree = HexagonCover.NBand.M8500_8700.SplitData.node2960 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2961
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2986

def B2959 : Block := .branch 159 ![5193565747075390293469247098061185, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 945).pointIds 945), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B2960]
theorem treeEq2959 : B2959.tree = HexagonCover.NBand.M8500_8700.SplitData.node2959 := by
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
  · exact treeEq2960

theorem accepted2959 : B2959.accepted = true := by decide +kernel
theorem checked2959 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2959 (maskNeeds ![5193565747075390293469247098061185, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2959]
  exact B2959.sound accepted2959
#print axioms checked2959

end HexagonCover.NBand.M8500_8700.SplitTree.Run0040
