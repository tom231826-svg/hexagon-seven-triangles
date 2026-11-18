import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0043
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0044
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip3158_3162 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3162 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] HexagonCover.NBand.M8500_8700.SplitTree.Run0043.checked3162
def B3181 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq3181 : B3181.tree = HexagonCover.NBand.M8500_8700.SplitData.node3181 := by
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

def B3180 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3181, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq3180 : B3180.tree = HexagonCover.NBand.M8500_8700.SplitData.node3180 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3181
  · rfl

def B3179 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B3180]
theorem treeEq3179 : B3179.tree = HexagonCover.NBand.M8500_8700.SplitData.node3179 := by
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
  · exact treeEq3180

def B3178 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B3179, (.leaf 0 [] 0)]
theorem treeEq3178 : B3178.tree = HexagonCover.NBand.M8500_8700.SplitData.node3178 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3179
  · rfl

def B3177 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B3178, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3177 : B3177.tree = HexagonCover.NBand.M8500_8700.SplitData.node3177 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3178
  · rfl

def B3161 : Block := .branch 119 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip3158_3162, B3177, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq3161 : B3161.tree = HexagonCover.NBand.M8500_8700.SplitData.node3161 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3177
  · rfl
  · rfl

def B3184 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq3184 : B3184.tree = HexagonCover.NBand.M8500_8700.SplitData.node3184 := by
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

def B3183 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B3184, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq3183 : B3183.tree = HexagonCover.NBand.M8500_8700.SplitData.node3183 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3184
  · rfl
  · rfl
  · rfl
  · rfl

def B3182 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B3183, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq3182 : B3182.tree = HexagonCover.NBand.M8500_8700.SplitData.node3182 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3183
  · rfl
  · rfl
  · rfl

def B3160 : Block := .branch 114 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B3161, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B3182]
theorem treeEq3160 : B3160.tree = HexagonCover.NBand.M8500_8700.SplitData.node3160 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3161
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3182

def B3189 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq3189 : B3189.tree = HexagonCover.NBand.M8500_8700.SplitData.node3189 := by
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

def B3188 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3189, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq3188 : B3188.tree = HexagonCover.NBand.M8500_8700.SplitData.node3188 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3189
  · rfl

def B3187 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3188]
theorem treeEq3187 : B3187.tree = HexagonCover.NBand.M8500_8700.SplitData.node3187 := by
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
  · exact treeEq3188

def B3186 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 851).pointIds 851), B3187, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq3186 : B3186.tree = HexagonCover.NBand.M8500_8700.SplitData.node3186 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3187
  · rfl
  · rfl
  · rfl

def B3185 : Block := .branch 160 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), B3186, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq3185 : B3185.tree = HexagonCover.NBand.M8500_8700.SplitData.node3185 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3186
  · rfl
  · rfl
  · rfl
  · rfl

def B3159 : Block := .branch 113 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B3160, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B3185]
theorem treeEq3159 : B3159.tree = HexagonCover.NBand.M8500_8700.SplitData.node3159 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3160
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3185

def B3158 : Block := .branch 159 ![5192298715444886558852708491592065, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 929).pointIds 929), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B3159]
theorem treeEq3158 : B3158.tree = HexagonCover.NBand.M8500_8700.SplitData.node3158 := by
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
  · exact treeEq3159

theorem accepted3158 : B3158.accepted = true := by decide +kernel
theorem checked3158 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3158 (maskNeeds ![5192298715444886558852708491592065, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3158]
  exact B3158.sound accepted3158
#print axioms checked3158

def Tip3157_3194 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3194 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] HexagonCover.NBand.M8500_8700.SplitTree.Run0043.checked3194
def Tip3157_3158 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3158 ![5192298715444886558852708491592065, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] checked3158
def B3213 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq3213 : B3213.tree = HexagonCover.NBand.M8500_8700.SplitData.node3213 := by
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

def B3212 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3213, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq3212 : B3212.tree = HexagonCover.NBand.M8500_8700.SplitData.node3212 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3213
  · rfl

def B3211 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B3212]
theorem treeEq3211 : B3211.tree = HexagonCover.NBand.M8500_8700.SplitData.node3211 := by
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
  · exact treeEq3212

def B3210 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B3211, (.leaf 0 [] 0)]
theorem treeEq3210 : B3210.tree = HexagonCover.NBand.M8500_8700.SplitData.node3210 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3211
  · rfl

def B3209 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B3210, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3209 : B3209.tree = HexagonCover.NBand.M8500_8700.SplitData.node3209 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3210
  · rfl

def B3193 : Block := .branch 119 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip3157_3194, B3209, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq3193 : B3193.tree = HexagonCover.NBand.M8500_8700.SplitData.node3193 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3209
  · rfl
  · rfl

def B3216 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq3216 : B3216.tree = HexagonCover.NBand.M8500_8700.SplitData.node3216 := by
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

def B3215 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B3216, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq3215 : B3215.tree = HexagonCover.NBand.M8500_8700.SplitData.node3215 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3216
  · rfl
  · rfl
  · rfl
  · rfl

def B3214 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B3215, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq3214 : B3214.tree = HexagonCover.NBand.M8500_8700.SplitData.node3214 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3215
  · rfl
  · rfl
  · rfl

def B3192 : Block := .branch 114 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![B3193, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B3214]
theorem treeEq3192 : B3192.tree = HexagonCover.NBand.M8500_8700.SplitData.node3192 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3193
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3214

def B3191 : Block := .branch 159 ![10385863224579942416784701524017537, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 939).pointIds 939), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B3192]
theorem treeEq3191 : B3191.tree = HexagonCover.NBand.M8500_8700.SplitData.node3191 := by
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
  · exact treeEq3192

def B3221 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq3221 : B3221.tree = HexagonCover.NBand.M8500_8700.SplitData.node3221 := by
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

def B3220 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3221, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq3220 : B3220.tree = HexagonCover.NBand.M8500_8700.SplitData.node3220 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3221
  · rfl

def B3219 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3220]
theorem treeEq3219 : B3219.tree = HexagonCover.NBand.M8500_8700.SplitData.node3219 := by
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
  · exact treeEq3220

def B3218 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 851).pointIds 851), B3219, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq3218 : B3218.tree = HexagonCover.NBand.M8500_8700.SplitData.node3218 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3219
  · rfl
  · rfl
  · rfl

def B3217 : Block := .branch 160 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), B3218, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq3217 : B3217.tree = HexagonCover.NBand.M8500_8700.SplitData.node3217 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3218
  · rfl
  · rfl
  · rfl
  · rfl

def B3190 : Block := .branch 113 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![B3191, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B3217]
theorem treeEq3190 : B3190.tree = HexagonCover.NBand.M8500_8700.SplitData.node3190 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3191
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3217

def B3157 : Block := .branch 112 ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip3157_3158, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B3190]
theorem treeEq3157 : B3157.tree = HexagonCover.NBand.M8500_8700.SplitData.node3157 := by
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
  · exact treeEq3190

theorem accepted3157 : B3157.accepted = true := by decide +kernel
theorem checked3157 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3157 (maskNeeds ![1269507510287159723708865577345, 151116339941927725041154, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq3157]
  exact B3157.sound accepted3157
#print axioms checked3157

def B3250 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq3250 : B3250.tree = HexagonCover.NBand.M8500_8700.SplitData.node3250 := by
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

def B3249 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3250, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq3249 : B3249.tree = HexagonCover.NBand.M8500_8700.SplitData.node3249 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3250
  · rfl

def B3248 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3249]
theorem treeEq3248 : B3248.tree = HexagonCover.NBand.M8500_8700.SplitData.node3248 := by
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
  · exact treeEq3249

def B3255 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq3255 : B3255.tree = HexagonCover.NBand.M8500_8700.SplitData.node3255 := by
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

def B3254 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3255, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq3254 : B3254.tree = HexagonCover.NBand.M8500_8700.SplitData.node3254 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3255
  · rfl

def B3253 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B3254]
theorem treeEq3253 : B3253.tree = HexagonCover.NBand.M8500_8700.SplitData.node3253 := by
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
  · exact treeEq3254

def B3252 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B3253, (.leaf 0 [] 0)]
theorem treeEq3252 : B3252.tree = HexagonCover.NBand.M8500_8700.SplitData.node3252 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3253
  · rfl

def B3251 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B3252, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3251 : B3251.tree = HexagonCover.NBand.M8500_8700.SplitData.node3251 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3252
  · rfl

def B3247 : Block := .branch 129 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B3248, B3251, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq3247 : B3247.tree = HexagonCover.NBand.M8500_8700.SplitData.node3247 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3248
  · exact treeEq3251
  · rfl
  · rfl

def B3260 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq3260 : B3260.tree = HexagonCover.NBand.M8500_8700.SplitData.node3260 := by
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

def B3259 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B3260, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq3259 : B3259.tree = HexagonCover.NBand.M8500_8700.SplitData.node3259 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3260
  · rfl
  · rfl
  · rfl
  · rfl

def B3258 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B3259, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3258 : B3258.tree = HexagonCover.NBand.M8500_8700.SplitData.node3258 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3259
  · rfl
  · rfl
  · rfl

def B3257 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3258]
theorem treeEq3257 : B3257.tree = HexagonCover.NBand.M8500_8700.SplitData.node3257 := by
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
  · exact treeEq3258

def B3256 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3257, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq3256 : B3256.tree = HexagonCover.NBand.M8500_8700.SplitData.node3256 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3257
  · rfl

def B3246 : Block := .branch 121 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B3247, (.leaf 5 (Common.fact 319).pointIds 319), B3256]
theorem treeEq3246 : B3246.tree = HexagonCover.NBand.M8500_8700.SplitData.node3246 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3247
  · rfl
  · exact treeEq3256

theorem accepted3246 : B3246.accepted = true := by decide +kernel
theorem checked3246 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3246 (maskNeeds ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq3246]
  exact B3246.sound accepted3246
#print axioms checked3246

def B3282 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq3282 : B3282.tree = HexagonCover.NBand.M8500_8700.SplitData.node3282 := by
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

def B3281 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3282, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq3281 : B3281.tree = HexagonCover.NBand.M8500_8700.SplitData.node3281 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3282
  · rfl

def B3280 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3281]
theorem treeEq3280 : B3280.tree = HexagonCover.NBand.M8500_8700.SplitData.node3280 := by
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
  · exact treeEq3281

def B3287 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq3287 : B3287.tree = HexagonCover.NBand.M8500_8700.SplitData.node3287 := by
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

def B3286 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3287, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq3286 : B3286.tree = HexagonCover.NBand.M8500_8700.SplitData.node3286 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3287
  · rfl

def B3285 : Block := .branch 163 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B3286]
theorem treeEq3285 : B3285.tree = HexagonCover.NBand.M8500_8700.SplitData.node3285 := by
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
  · exact treeEq3286

def B3284 : Block := .branch 165 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B3285, (.leaf 0 [] 0)]
theorem treeEq3284 : B3284.tree = HexagonCover.NBand.M8500_8700.SplitData.node3284 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3285
  · rfl

def B3283 : Block := .branch 167 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B3284, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq3283 : B3283.tree = HexagonCover.NBand.M8500_8700.SplitData.node3283 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3284
  · rfl

def B3279 : Block := .branch 129 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B3280, B3283, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq3279 : B3279.tree = HexagonCover.NBand.M8500_8700.SplitData.node3279 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3280
  · exact treeEq3283
  · rfl
  · rfl

def B3292 : Block := .branch 160 ![385, 151116339941927725041154, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq3292 : B3292.tree = HexagonCover.NBand.M8500_8700.SplitData.node3292 := by
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

def B3291 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), B3292, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq3291 : B3291.tree = HexagonCover.NBand.M8500_8700.SplitData.node3291 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3292
  · rfl
  · rfl
  · rfl
  · rfl

def B3290 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), B3291, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq3290 : B3290.tree = HexagonCover.NBand.M8500_8700.SplitData.node3290 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3291
  · rfl
  · rfl
  · rfl

def B3289 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B3290]
theorem treeEq3289 : B3289.tree = HexagonCover.NBand.M8500_8700.SplitData.node3289 := by
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
  · exact treeEq3290

def B3288 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3289, (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq3288 : B3288.tree = HexagonCover.NBand.M8500_8700.SplitData.node3288 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3289
  · rfl

def B3278 : Block := .branch 121 ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B3279, (.leaf 5 (Common.fact 319).pointIds 319), B3288]
theorem treeEq3278 : B3278.tree = HexagonCover.NBand.M8500_8700.SplitData.node3278 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3279
  · rfl
  · exact treeEq3288

theorem accepted3278 : B3278.accepted = true := by decide +kernel
theorem checked3278 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3278 (maskNeeds ![1237940039287632074712809857, 151116339941927725041154, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032]) := by
  rw [← treeEq3278]
  exact B3278.sound accepted3278
#print axioms checked3278

end HexagonCover.NBand.M8500_8700.SplitTree.Run0044
