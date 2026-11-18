import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0024
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0025
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1820_1857 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1857 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] HexagonCover.NBand.M8500_8700.SplitTree.Run0024.checked1857
def Tip1820_1821 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1821 ![5193565747075095722024820048658817, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0024.checked1821
def B1876 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq1876 : B1876.tree = HexagonCover.NBand.M8500_8700.SplitData.node1876 := by
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

def B1875 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1876, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq1875 : B1875.tree = HexagonCover.NBand.M8500_8700.SplitData.node1875 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1876
  · rfl

def B1874 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B1875]
theorem treeEq1874 : B1874.tree = HexagonCover.NBand.M8500_8700.SplitData.node1874 := by
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
  · exact treeEq1875

def B1873 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B1874, (.leaf 0 [] 0)]
theorem treeEq1873 : B1873.tree = HexagonCover.NBand.M8500_8700.SplitData.node1873 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1874
  · rfl

def B1872 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B1873, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1872 : B1872.tree = HexagonCover.NBand.M8500_8700.SplitData.node1872 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1873
  · rfl

def B1856 : Block := .branch 119 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip1820_1857, B1872, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq1856 : B1856.tree = HexagonCover.NBand.M8500_8700.SplitData.node1856 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1872
  · rfl
  · rfl

def B1879 : Block := .branch 160 ![385, 151447768845705174582786, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq1879 : B1879.tree = HexagonCover.NBand.M8500_8700.SplitData.node1879 := by
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

def B1878 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), B1879, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1878 : B1878.tree = HexagonCover.NBand.M8500_8700.SplitData.node1878 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1879
  · rfl
  · rfl
  · rfl
  · rfl

def B1877 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), B1878, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1877 : B1877.tree = HexagonCover.NBand.M8500_8700.SplitData.node1877 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1878
  · rfl
  · rfl
  · rfl

def B1855 : Block := .branch 114 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![B1856, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B1877]
theorem treeEq1855 : B1855.tree = HexagonCover.NBand.M8500_8700.SplitData.node1855 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1856
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1877

def B1854 : Block := .branch 159 ![10385862605609923350555316377878913, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 913).pointIds 913), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1855]
theorem treeEq1854 : B1854.tree = HexagonCover.NBand.M8500_8700.SplitData.node1854 := by
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
  · exact treeEq1855

def B1884 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1884 : B1884.tree = HexagonCover.NBand.M8500_8700.SplitData.node1884 := by
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

def B1883 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1884, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1883 : B1883.tree = HexagonCover.NBand.M8500_8700.SplitData.node1883 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1884
  · rfl

def B1882 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1883]
theorem treeEq1882 : B1882.tree = HexagonCover.NBand.M8500_8700.SplitData.node1882 := by
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
  · exact treeEq1883

def B1881 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 851).pointIds 851), B1882, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1881 : B1881.tree = HexagonCover.NBand.M8500_8700.SplitData.node1881 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1882
  · rfl
  · rfl
  · rfl

def B1880 : Block := .branch 160 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), B1881, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq1880 : B1880.tree = HexagonCover.NBand.M8500_8700.SplitData.node1880 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1881
  · rfl
  · rfl
  · rfl
  · rfl

def B1853 : Block := .branch 113 ![1268888540268093494323719438721, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![B1854, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1880]
theorem treeEq1853 : B1853.tree = HexagonCover.NBand.M8500_8700.SplitData.node1853 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1854
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1880

def B1820 : Block := .branch 112 ![1268888540268093494323719438721, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip1820_1821, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1853]
theorem treeEq1820 : B1820.tree = HexagonCover.NBand.M8500_8700.SplitData.node1820 := by
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
  · exact treeEq1853

theorem accepted1820 : B1820.accepted = true := by decide +kernel
theorem checked1820 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1820 (maskNeeds ![1268888540268093494323719438721, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1820]
  exact B1820.sound accepted1820
#print axioms checked1820

def Tip1732_1736 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1736 ![1269507510287736184461169000833, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0024.checked1736
def B1802 : Block := .branch 168 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1802 : B1802.tree = HexagonCover.NBand.M8500_8700.SplitData.node1802 := by
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

def B1801 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1802, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1801 : B1801.tree = HexagonCover.NBand.M8500_8700.SplitData.node1801 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1802
  · rfl

def B1735 : Block := .branch 109 ![1269507510287736184461169000833, 151447768845705174582786, 9709185488779990559365124, 325073155631729855604827527077896, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip1732_1736, (.leaf 5 (Common.fact 294).pointIds 294), B1801]
theorem treeEq1735 : B1735.tree = HexagonCover.NBand.M8500_8700.SplitData.node1735 := by
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
  · exact treeEq1801

def B1807 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1807 : B1807.tree = HexagonCover.NBand.M8500_8700.SplitData.node1807 := by
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

def B1806 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1807, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1806 : B1806.tree = HexagonCover.NBand.M8500_8700.SplitData.node1806 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1807
  · rfl

def B1805 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1806]
theorem treeEq1805 : B1805.tree = HexagonCover.NBand.M8500_8700.SplitData.node1805 := by
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
  · exact treeEq1806

def B1804 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1805, (.leaf 0 [] 0)]
theorem treeEq1804 : B1804.tree = HexagonCover.NBand.M8500_8700.SplitData.node1804 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1805
  · rfl

def B1803 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1804, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1803 : B1803.tree = HexagonCover.NBand.M8500_8700.SplitData.node1803 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1804
  · rfl

def B1734 : Block := .branch 108 ![1269507510287736184461169000833, 151447768845705174582786, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B1735, B1803, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1734 : B1734.tree = HexagonCover.NBand.M8500_8700.SplitData.node1734 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1735
  · exact treeEq1803
  · rfl
  · rfl

def B1810 : Block := .branch 160 ![385, 151447768845705174582786, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1810 : B1810.tree = HexagonCover.NBand.M8500_8700.SplitData.node1810 := by
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

def B1809 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), B1810, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1809 : B1809.tree = HexagonCover.NBand.M8500_8700.SplitData.node1809 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1810
  · rfl
  · rfl
  · rfl
  · rfl

def B1808 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), B1809, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1808 : B1808.tree = HexagonCover.NBand.M8500_8700.SplitData.node1808 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1809
  · rfl
  · rfl
  · rfl

def B1733 : Block := .branch 100 ![1856910059506782964465795457, 151447768845705174582786, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B1734, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1808]
theorem treeEq1733 : B1733.tree = HexagonCover.NBand.M8500_8700.SplitData.node1733 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1734
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1808

def B1815 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1815 : B1815.tree = HexagonCover.NBand.M8500_8700.SplitData.node1815 := by
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

def B1814 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1815, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1814 : B1814.tree = HexagonCover.NBand.M8500_8700.SplitData.node1814 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1815
  · rfl

def B1813 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1814]
theorem treeEq1813 : B1813.tree = HexagonCover.NBand.M8500_8700.SplitData.node1813 := by
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
  · exact treeEq1814

def B1812 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1813, (.leaf 0 [] 0)]
theorem treeEq1812 : B1812.tree = HexagonCover.NBand.M8500_8700.SplitData.node1812 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1813
  · rfl

def B1811 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1812, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1811 : B1811.tree = HexagonCover.NBand.M8500_8700.SplitData.node1811 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1812
  · rfl

def B1732 : Block := .branch 98 ![1856910059506782964465795457, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1733, B1811, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1732 : B1732.tree = HexagonCover.NBand.M8500_8700.SplitData.node1732 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1733
  · exact treeEq1811
  · rfl
  · rfl

theorem accepted1732 : B1732.accepted = true := by decide +kernel
theorem checked1732 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1732 (maskNeeds ![1856910059506782964465795457, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1732]
  exact B1732.sound accepted1732
#print axioms checked1732

def Tip1731_1820 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1820 ![1268888540268093494323719438721, 151447768845705174582786, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] checked1820
def Tip1731_1732 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1732 ![1856910059506782964465795457, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] checked1732
def B1886 : Block := .branch 168 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1886 : B1886.tree = HexagonCover.NBand.M8500_8700.SplitData.node1886 := by
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

def B1885 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1886, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1885 : B1885.tree = HexagonCover.NBand.M8500_8700.SplitData.node1885 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1886
  · rfl

def B1819 : Block := .branch 109 ![1268888540268093494323719438721, 151447768845705174582786, 9709185488779990559365124, 325073155631729855604827527077896, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), Tip1731_1820, (.leaf 5 (Common.fact 294).pointIds 294), B1885]
theorem treeEq1819 : B1819.tree = HexagonCover.NBand.M8500_8700.SplitData.node1819 := by
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
  · exact treeEq1885

def B1891 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1891 : B1891.tree = HexagonCover.NBand.M8500_8700.SplitData.node1891 := by
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

def B1890 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1891, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1890 : B1890.tree = HexagonCover.NBand.M8500_8700.SplitData.node1890 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1891
  · rfl

def B1889 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1890]
theorem treeEq1889 : B1889.tree = HexagonCover.NBand.M8500_8700.SplitData.node1889 := by
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
  · exact treeEq1890

def B1888 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1889, (.leaf 0 [] 0)]
theorem treeEq1888 : B1888.tree = HexagonCover.NBand.M8500_8700.SplitData.node1888 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1889
  · rfl

def B1887 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1888, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1887 : B1887.tree = HexagonCover.NBand.M8500_8700.SplitData.node1887 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1888
  · rfl

def B1818 : Block := .branch 108 ![1268888540268093494323719438721, 151447768845705174582786, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B1819, B1887, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1818 : B1818.tree = HexagonCover.NBand.M8500_8700.SplitData.node1818 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1819
  · exact treeEq1887
  · rfl
  · rfl

def B1894 : Block := .branch 160 ![385, 151447768845705174582786, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1894 : B1894.tree = HexagonCover.NBand.M8500_8700.SplitData.node1894 := by
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

def B1893 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), B1894, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1893 : B1893.tree = HexagonCover.NBand.M8500_8700.SplitData.node1893 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1894
  · rfl
  · rfl
  · rfl
  · rfl

def B1892 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), B1893, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1892 : B1892.tree = HexagonCover.NBand.M8500_8700.SplitData.node1892 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1893
  · rfl
  · rfl
  · rfl

def B1817 : Block := .branch 100 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B1818, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1892]
theorem treeEq1817 : B1817.tree = HexagonCover.NBand.M8500_8700.SplitData.node1817 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1818
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1892

def B1899 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1899 : B1899.tree = HexagonCover.NBand.M8500_8700.SplitData.node1899 := by
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

def B1898 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1899, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1898 : B1898.tree = HexagonCover.NBand.M8500_8700.SplitData.node1898 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1899
  · rfl

def B1897 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1898]
theorem treeEq1897 : B1897.tree = HexagonCover.NBand.M8500_8700.SplitData.node1897 := by
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
  · exact treeEq1898

def B1896 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1897, (.leaf 0 [] 0)]
theorem treeEq1896 : B1896.tree = HexagonCover.NBand.M8500_8700.SplitData.node1896 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1897
  · rfl

def B1895 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1896, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1895 : B1895.tree = HexagonCover.NBand.M8500_8700.SplitData.node1895 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1896
  · rfl

def B1816 : Block := .branch 98 ![1237940039864092827016233345, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1817, B1895, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1816 : B1816.tree = HexagonCover.NBand.M8500_8700.SplitData.node1816 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1817
  · exact treeEq1895
  · rfl
  · rfl

def B1731 : Block := .branch 89 ![1237940039864092827016233345, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![Tip1731_1732, B1816, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq1731 : B1731.tree = HexagonCover.NBand.M8500_8700.SplitData.node1731 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1816
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1731 : B1731.accepted = true := by decide +kernel
theorem checked1731 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1731 (maskNeeds ![1237940039864092827016233345, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1731]
  exact B1731.sound accepted1731
#print axioms checked1731

def Tip1726_1731 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1731 ![1237940039864092827016233345, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] checked1731
def B1901 : Block := .branch 160 ![385, 151447768845705174582786, 357842042605930235713034244, 24584, 98320, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq1901 : B1901.tree = HexagonCover.NBand.M8500_8700.SplitData.node1901 := by
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

def B1900 : Block := .branch 161 ![385, 151447768845705174582786, 357842042605930235713034244, 158461160731807133703786749960, 98320, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 856).pointIds 856), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B1901]
theorem treeEq1900 : B1900.tree = HexagonCover.NBand.M8500_8700.SplitData.node1900 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1901

def B1730 : Block := .branch 88 ![1237940039864092827016233345, 151447768845705174582786, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), Tip1726_1731, B1900, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq1730 : B1730.tree = HexagonCover.NBand.M8500_8700.SplitData.node1730 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1900
  · rfl
  · rfl
  · rfl
  · rfl

def B1904 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1904 : B1904.tree = HexagonCover.NBand.M8500_8700.SplitData.node1904 := by
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

def B1903 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1904, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1903 : B1903.tree = HexagonCover.NBand.M8500_8700.SplitData.node1903 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1904
  · rfl

def B1902 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158538531984262469970967945224, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1903]
theorem treeEq1902 : B1902.tree = HexagonCover.NBand.M8500_8700.SplitData.node1902 := by
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
  · exact treeEq1903

def B1729 : Block := .branch 86 ![1237940039864092827016233345, 151447768845705174582786, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B1730, B1902, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq1729 : B1729.tree = HexagonCover.NBand.M8500_8700.SplitData.node1729 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1730
  · exact treeEq1902
  · rfl
  · rfl
  · rfl

def B1907 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1907 : B1907.tree = HexagonCover.NBand.M8500_8700.SplitData.node1907 := by
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

def B1906 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1907, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1906 : B1906.tree = HexagonCover.NBand.M8500_8700.SplitData.node1906 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1907
  · rfl

def B1905 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1906]
theorem treeEq1905 : B1905.tree = HexagonCover.NBand.M8500_8700.SplitData.node1905 := by
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
  · exact treeEq1906

def B1728 : Block := .branch 85 ![1237940039864092827016233345, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B1729, B1905, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq1728 : B1728.tree = HexagonCover.NBand.M8500_8700.SplitData.node1728 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1729
  · exact treeEq1905
  · rfl
  · rfl
  · rfl

def B1910 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1910 : B1910.tree = HexagonCover.NBand.M8500_8700.SplitData.node1910 := by
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

def B1909 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1910, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1909 : B1909.tree = HexagonCover.NBand.M8500_8700.SplitData.node1909 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1910
  · rfl

def B1908 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1909]
theorem treeEq1908 : B1908.tree = HexagonCover.NBand.M8500_8700.SplitData.node1908 := by
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
  · exact treeEq1909

def B1727 : Block := .branch 84 ![1237940039864092827016233345, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B1728, B1908, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq1727 : B1727.tree = HexagonCover.NBand.M8500_8700.SplitData.node1727 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1728
  · exact treeEq1908
  · rfl
  · rfl
  · rfl

def B1913 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1913 : B1913.tree = HexagonCover.NBand.M8500_8700.SplitData.node1913 := by
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

def B1912 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1913, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1912 : B1912.tree = HexagonCover.NBand.M8500_8700.SplitData.node1912 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1913
  · rfl

def B1911 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1912]
theorem treeEq1911 : B1911.tree = HexagonCover.NBand.M8500_8700.SplitData.node1911 := by
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
  · exact treeEq1912

def B1726 : Block := .branch 83 ![1237940039864092827016233345, 151447768845705174582786, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B1727, B1911, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq1726 : B1726.tree = HexagonCover.NBand.M8500_8700.SplitData.node1726 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1727
  · exact treeEq1911
  · rfl
  · rfl
  · rfl

theorem accepted1726 : B1726.accepted = true := by decide +kernel
theorem checked1726 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1726 (maskNeeds ![1237940039864092827016233345, 151447768845705174582786, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq1726]
  exact B1726.sound accepted1726
#print axioms checked1726

end HexagonCover.NBand.M8500_8700.SplitTree.Run0025
