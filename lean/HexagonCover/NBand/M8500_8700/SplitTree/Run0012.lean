import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0011
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0012
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0894_0898 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0898 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] HexagonCover.NBand.M8500_8700.SplitTree.Run0011.checked0898
def B0917 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0917 : B0917.tree = HexagonCover.NBand.M8500_8700.SplitData.node0917 := by
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

def B0916 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0917, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0916 : B0916.tree = HexagonCover.NBand.M8500_8700.SplitData.node0916 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0917
  · rfl

def B0915 : Block := .branch 163 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0916]
theorem treeEq0915 : B0915.tree = HexagonCover.NBand.M8500_8700.SplitData.node0915 := by
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
  · exact treeEq0916

def B0914 : Block := .branch 165 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0915, (.leaf 0 [] 0)]
theorem treeEq0914 : B0914.tree = HexagonCover.NBand.M8500_8700.SplitData.node0914 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0915
  · rfl

def B0913 : Block := .branch 167 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0914, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0913 : B0913.tree = HexagonCover.NBand.M8500_8700.SplitData.node0913 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0914
  · rfl

def B0897 : Block := .branch 119 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip0894_0898, B0913, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0897 : B0897.tree = HexagonCover.NBand.M8500_8700.SplitData.node0897 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0913
  · rfl
  · rfl

def B0920 : Block := .branch 160 ![385, 377789318630121372911106, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0920 : B0920.tree = HexagonCover.NBand.M8500_8700.SplitData.node0920 := by
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

def B0919 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), B0920, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0919 : B0919.tree = HexagonCover.NBand.M8500_8700.SplitData.node0919 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0920
  · rfl
  · rfl
  · rfl
  · rfl

def B0918 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), B0919, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0918 : B0918.tree = HexagonCover.NBand.M8500_8700.SplitData.node0918 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0919
  · rfl
  · rfl
  · rfl

def B0896 : Block := .branch 114 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B0897, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0918]
theorem treeEq0896 : B0896.tree = HexagonCover.NBand.M8500_8700.SplitData.node0896 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0897
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0918

def B0925 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0925 : B0925.tree = HexagonCover.NBand.M8500_8700.SplitData.node0925 := by
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

def B0924 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0925, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0924 : B0924.tree = HexagonCover.NBand.M8500_8700.SplitData.node0924 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0925
  · rfl

def B0923 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0924]
theorem treeEq0923 : B0923.tree = HexagonCover.NBand.M8500_8700.SplitData.node0923 := by
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
  · exact treeEq0924

def B0922 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 851).pointIds 851), B0923, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0922 : B0922.tree = HexagonCover.NBand.M8500_8700.SplitData.node0922 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0923
  · rfl
  · rfl
  · rfl

def B0921 : Block := .branch 160 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), B0922, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0921 : B0921.tree = HexagonCover.NBand.M8500_8700.SplitData.node0921 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0922
  · rfl
  · rfl
  · rfl
  · rfl

def B0895 : Block := .branch 113 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B0896, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0921]
theorem treeEq0895 : B0895.tree = HexagonCover.NBand.M8500_8700.SplitData.node0895 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0896
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0921

def B0894 : Block := .branch 159 ![5192298715445182283218640147841409, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 363).pointIds 363), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0895]
theorem treeEq0894 : B0894.tree = HexagonCover.NBand.M8500_8700.SplitData.node0894 := by
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
  · exact treeEq0895

theorem accepted0894 : B0894.accepted = true := by decide +kernel
theorem checked0894 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0894 (maskNeeds ![5192298715445182283218640147841409, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0894]
  exact B0894.sound accepted0894
#print axioms checked0894

def Tip0893_0930 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0930 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] HexagonCover.NBand.M8500_8700.SplitTree.Run0011.checked0930
def Tip0893_0894 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0894 ![5192298715445182283218640147841409, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] checked0894
def B0949 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq0949 : B0949.tree = HexagonCover.NBand.M8500_8700.SplitData.node0949 := by
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

def B0948 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0949, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq0948 : B0948.tree = HexagonCover.NBand.M8500_8700.SplitData.node0948 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0949
  · rfl

def B0947 : Block := .branch 163 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0948]
theorem treeEq0947 : B0947.tree = HexagonCover.NBand.M8500_8700.SplitData.node0947 := by
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
  · exact treeEq0948

def B0946 : Block := .branch 165 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0947, (.leaf 0 [] 0)]
theorem treeEq0946 : B0946.tree = HexagonCover.NBand.M8500_8700.SplitData.node0946 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0947
  · rfl

def B0945 : Block := .branch 167 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0946, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0945 : B0945.tree = HexagonCover.NBand.M8500_8700.SplitData.node0945 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0946
  · rfl

def B0929 : Block := .branch 119 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip0893_0930, B0945, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0929 : B0929.tree = HexagonCover.NBand.M8500_8700.SplitData.node0929 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0945
  · rfl
  · rfl

def B0952 : Block := .branch 160 ![385, 377789318630121372911106, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0952 : B0952.tree = HexagonCover.NBand.M8500_8700.SplitData.node0952 := by
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

def B0951 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), B0952, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0951 : B0951.tree = HexagonCover.NBand.M8500_8700.SplitData.node0951 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0952
  · rfl
  · rfl
  · rfl
  · rfl

def B0950 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), B0951, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0950 : B0950.tree = HexagonCover.NBand.M8500_8700.SplitData.node0950 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0951
  · rfl
  · rfl
  · rfl

def B0928 : Block := .branch 114 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![B0929, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0950]
theorem treeEq0928 : B0928.tree = HexagonCover.NBand.M8500_8700.SplitData.node0928 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0929
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0950

def B0927 : Block := .branch 159 ![10385863224580238141150633180266881, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0928]
theorem treeEq0927 : B0927.tree = HexagonCover.NBand.M8500_8700.SplitData.node0927 := by
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
  · exact treeEq0928

def B0957 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0957 : B0957.tree = HexagonCover.NBand.M8500_8700.SplitData.node0957 := by
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

def B0956 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0957, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0956 : B0956.tree = HexagonCover.NBand.M8500_8700.SplitData.node0956 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0957
  · rfl

def B0955 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0956]
theorem treeEq0955 : B0955.tree = HexagonCover.NBand.M8500_8700.SplitData.node0955 := by
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
  · exact treeEq0956

def B0954 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 851).pointIds 851), B0955, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0954 : B0954.tree = HexagonCover.NBand.M8500_8700.SplitData.node0954 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0955
  · rfl
  · rfl
  · rfl

def B0953 : Block := .branch 160 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), B0954, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0953 : B0953.tree = HexagonCover.NBand.M8500_8700.SplitData.node0953 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0954
  · rfl
  · rfl
  · rfl
  · rfl

def B0926 : Block := .branch 113 ![1269507510582884089640521826689, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![B0927, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0953]
theorem treeEq0926 : B0926.tree = HexagonCover.NBand.M8500_8700.SplitData.node0926 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0927
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0953

def B0893 : Block := .branch 112 ![1269507510582884089640521826689, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip0893_0894, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B0926]
theorem treeEq0893 : B0893.tree = HexagonCover.NBand.M8500_8700.SplitData.node0893 := by
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
  · exact treeEq0926

theorem accepted0893 : B0893.accepted = true := by decide +kernel
theorem checked0893 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0893 (maskNeeds ![1269507510582884089640521826689, 377789318630121372911106, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0893]
  exact B0893.sound accepted0893
#print axioms checked0893

def B0986 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0986 : B0986.tree = HexagonCover.NBand.M8500_8700.SplitData.node0986 := by
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

def B0985 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0986, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0985 : B0985.tree = HexagonCover.NBand.M8500_8700.SplitData.node0985 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0986
  · rfl

def B0984 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0985]
theorem treeEq0984 : B0984.tree = HexagonCover.NBand.M8500_8700.SplitData.node0984 := by
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
  · exact treeEq0985

def B0991 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0991 : B0991.tree = HexagonCover.NBand.M8500_8700.SplitData.node0991 := by
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

def B0990 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0991, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0990 : B0990.tree = HexagonCover.NBand.M8500_8700.SplitData.node0990 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0991
  · rfl

def B0989 : Block := .branch 163 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0990]
theorem treeEq0989 : B0989.tree = HexagonCover.NBand.M8500_8700.SplitData.node0989 := by
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
  · exact treeEq0990

def B0988 : Block := .branch 165 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0989, (.leaf 0 [] 0)]
theorem treeEq0988 : B0988.tree = HexagonCover.NBand.M8500_8700.SplitData.node0988 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0989
  · rfl

def B0987 : Block := .branch 167 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0988, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0987 : B0987.tree = HexagonCover.NBand.M8500_8700.SplitData.node0987 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0988
  · rfl

def B0983 : Block := .branch 129 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0984, B0987, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0983 : B0983.tree = HexagonCover.NBand.M8500_8700.SplitData.node0983 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0984
  · exact treeEq0987
  · rfl
  · rfl

def B0996 : Block := .branch 160 ![385, 377789318630121372911106, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0996 : B0996.tree = HexagonCover.NBand.M8500_8700.SplitData.node0996 := by
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

def B0995 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), B0996, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0995 : B0995.tree = HexagonCover.NBand.M8500_8700.SplitData.node0995 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0996
  · rfl
  · rfl
  · rfl
  · rfl

def B0994 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), B0995, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0994 : B0994.tree = HexagonCover.NBand.M8500_8700.SplitData.node0994 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0995
  · rfl
  · rfl
  · rfl

def B0993 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0994]
theorem treeEq0993 : B0993.tree = HexagonCover.NBand.M8500_8700.SplitData.node0993 := by
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
  · exact treeEq0994

def B0992 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0993, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0992 : B0992.tree = HexagonCover.NBand.M8500_8700.SplitData.node0992 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0993
  · rfl

def B0982 : Block := .branch 121 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0983, (.leaf 5 (Common.fact 319).pointIds 319), B0992]
theorem treeEq0982 : B0982.tree = HexagonCover.NBand.M8500_8700.SplitData.node0982 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0983
  · rfl
  · exact treeEq0992

theorem accepted0982 : B0982.accepted = true := by decide +kernel
theorem checked0982 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0982 (maskNeeds ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq0982]
  exact B0982.sound accepted0982
#print axioms checked0982

def B1018 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1018 : B1018.tree = HexagonCover.NBand.M8500_8700.SplitData.node1018 := by
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

def B1017 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1018, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1017 : B1017.tree = HexagonCover.NBand.M8500_8700.SplitData.node1017 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1018
  · rfl

def B1016 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1017]
theorem treeEq1016 : B1016.tree = HexagonCover.NBand.M8500_8700.SplitData.node1016 := by
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
  · exact treeEq1017

def B1023 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq1023 : B1023.tree = HexagonCover.NBand.M8500_8700.SplitData.node1023 := by
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

def B1022 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1023, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq1022 : B1022.tree = HexagonCover.NBand.M8500_8700.SplitData.node1022 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1023
  · rfl

def B1021 : Block := .branch 163 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1022]
theorem treeEq1021 : B1021.tree = HexagonCover.NBand.M8500_8700.SplitData.node1021 := by
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
  · exact treeEq1022

def B1020 : Block := .branch 165 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1021, (.leaf 0 [] 0)]
theorem treeEq1020 : B1020.tree = HexagonCover.NBand.M8500_8700.SplitData.node1020 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1021
  · rfl

def B1019 : Block := .branch 167 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1020, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1019 : B1019.tree = HexagonCover.NBand.M8500_8700.SplitData.node1019 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1020
  · rfl

def B1015 : Block := .branch 129 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1016, B1019, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1015 : B1015.tree = HexagonCover.NBand.M8500_8700.SplitData.node1015 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1016
  · exact treeEq1019
  · rfl
  · rfl

def B1028 : Block := .branch 160 ![385, 377789318630121372911106, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1028 : B1028.tree = HexagonCover.NBand.M8500_8700.SplitData.node1028 := by
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

def B1027 : Block := .branch 172 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), B1028, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1027 : B1027.tree = HexagonCover.NBand.M8500_8700.SplitData.node1027 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1028
  · rfl
  · rfl
  · rfl
  · rfl

def B1026 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), B1027, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1026 : B1026.tree = HexagonCover.NBand.M8500_8700.SplitData.node1026 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1027
  · rfl
  · rfl
  · rfl

def B1025 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1026]
theorem treeEq1025 : B1025.tree = HexagonCover.NBand.M8500_8700.SplitData.node1025 := by
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
  · exact treeEq1026

def B1024 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1025, (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1024 : B1024.tree = HexagonCover.NBand.M8500_8700.SplitData.node1024 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1025
  · rfl

def B1014 : Block := .branch 121 ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B1015, (.leaf 5 (Common.fact 319).pointIds 319), B1024]
theorem treeEq1014 : B1014.tree = HexagonCover.NBand.M8500_8700.SplitData.node1014 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1015
  · rfl
  · exact treeEq1024

theorem accepted1014 : B1014.accepted = true := by decide +kernel
theorem checked1014 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1014 (maskNeeds ![1237940335011998006369059201, 377789318630121372911106, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032]) := by
  rw [← treeEq1014]
  exact B1014.sound accepted1014
#print axioms checked1014

end HexagonCover.NBand.M8500_8700.SplitTree.Run0012
