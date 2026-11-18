import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0092
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0093
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6746_6751 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6751 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] HexagonCover.NBand.M8300_8500.SplitTree.Run0092.checked6751
def B6750 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 928455029610473112563877378, 4835703278458516698830852, 348449144051717996569950853468473757032456, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), Tip6746_6751, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1091).pointIds 1091)]
theorem treeEq6750 : B6750.tree = HexagonCover.NBand.M8300_8500.SplitData.node6750 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6749 : Block := .branch 168 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 348449144051797224732465117806067300982792, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![B6750, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq6749 : B6749.tree = HexagonCover.NBand.M8300_8500.SplitData.node6749 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6750
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6748 : Block := .branch 170 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 348449144051797224732465117806067300982792, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 1089).pointIds 1089), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6749]
theorem treeEq6748 : B6748.tree = HexagonCover.NBand.M8300_8500.SplitData.node6748 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6749

def B6776 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 680565058518886910382004673206644924424, 2854843834556295840210475287950566715455275024, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1130).pointIds 1130), (.leaf 4 (Common.fact 1131).pointIds 1131), (.leaf 5 (Common.fact 1124).pointIds 1124), (.leaf 6 (Common.fact 1132).pointIds 1132)]
theorem treeEq6776 : B6776.tree = HexagonCover.NBand.M8300_8500.SplitData.node6776 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6775 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 928455029610473112563877378, 4835703278458516698830852, 680565058518886910382004673206644924424, 2854843834556295840210475287950566715455275024, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6776, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1129).pointIds 1129)]
theorem treeEq6775 : B6775.tree = HexagonCover.NBand.M8300_8500.SplitData.node6775 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6776
  · rfl
  · rfl
  · rfl
  · rfl

def B6774 : Block := .branch 168 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 680565058598115072896269010800188874760, 2854843834556295840210475287950566715455275024, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![B6775, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1128).pointIds 1128)]
theorem treeEq6774 : B6774.tree = HexagonCover.NBand.M8300_8500.SplitData.node6774 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6775
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6773 : Block := .branch 163 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 680565058598115072896269010800188874760, 2854843834556295840210475287950566715455275024, 233845970963757826047978923686416002951423709282336, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1127).pointIds 1127), (.leaf 5 (Common.fact 329).pointIds 329), B6774]
theorem treeEq6773 : B6773.tree = HexagonCover.NBand.M8300_8500.SplitData.node6773 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6774

def B6772 : Block := .branch 165 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 680565058598115072896269010800188874760, 2854843834556295840210475287950566715455275024, 187077918569168932665461009039494946322433867907104, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1126).pointIds 1126), B6773, (.leaf 0 [] 0)]
theorem treeEq6772 : B6772.tree = HexagonCover.NBand.M8300_8500.SplitData.node6772 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6773
  · rfl

def B6771 : Block := .branch 167 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 680565058598115072896269010800188874760, 2854843834556295840210475287950566715455275024, 5708990813359135389350451810719806474502406176, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1125).pointIds 1125), B6772, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6771 : B6771.tree = HexagonCover.NBand.M8300_8500.SplitData.node6771 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6772
  · rfl

def B6747 : Block := .branch 138 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 680565058598115072896269010800188874760, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444191588916126644288931732798581336575837732928] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), B6748, B6771, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6747 : B6747.tree = HexagonCover.NBand.M8300_8500.SplitData.node6747 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6748
  · exact treeEq6771
  · rfl
  · rfl

def B6782 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 664938674902441391707361873248673800, 2854496065977302641100815719101771448343166992, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1136).pointIds 1136), (.leaf 4 (Common.fact 1137).pointIds 1137), (.leaf 5 (Common.fact 1124).pointIds 1124), (.leaf 6 (Common.fact 1132).pointIds 1132)]
theorem treeEq6782 : B6782.tree = HexagonCover.NBand.M8300_8500.SplitData.node6782 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6781 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 928455029610473112563877378, 4835703278458516698830852, 664938674902441391707361873248673800, 2854496065977302641100815719101771448343166992, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6782, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1129).pointIds 1129)]
theorem treeEq6781 : B6781.tree = HexagonCover.NBand.M8300_8500.SplitData.node6781 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6782
  · rfl
  · rfl
  · rfl
  · rfl

def B6780 : Block := .branch 168 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854496065977302641100815719101771448343166992, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![B6781, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1128).pointIds 1128)]
theorem treeEq6780 : B6780.tree = HexagonCover.NBand.M8300_8500.SplitData.node6780 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6781
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6779 : Block := .branch 163 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854496065977302641100815719101771448343166992, 233845970963757826047978923686416002951423709282336, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1135).pointIds 1135), (.leaf 5 (Common.fact 329).pointIds 329), B6780]
theorem treeEq6779 : B6779.tree = HexagonCover.NBand.M8300_8500.SplitData.node6779 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6780

def B6778 : Block := .branch 165 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854496065977302641100815719101771448343166992, 187077918569168932665461009039494946322433867907104, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1134).pointIds 1134), B6779, (.leaf 0 [] 0)]
theorem treeEq6778 : B6778.tree = HexagonCover.NBand.M8300_8500.SplitData.node6778 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6779
  · rfl

def B6777 : Block := .branch 167 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854496065977302641100815719101771448343166992, 5708990813359135389350451810719806474502406176, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1133).pointIds 1133), B6778, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6777 : B6777.tree = HexagonCover.NBand.M8300_8500.SplitData.node6777 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6778
  · rfl

def B6746 : Block := .branch 129 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), B6747, B6777, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1088).pointIds 1088)]
theorem treeEq6746 : B6746.tree = HexagonCover.NBand.M8300_8500.SplitData.node6746 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6747
  · exact treeEq6777
  · rfl
  · rfl

theorem accepted6746 : B6746.accepted = true := by decide +kernel
theorem checked6746 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6746 (maskNeeds ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136]) := by
  rw [← treeEq6746]
  exact B6746.sound accepted6746
#print axioms checked6746

def Tip6738_6746 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6746 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664938754130603905971699466792624136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] checked6746
def B6744 : Block := .branch 163 ![385, 1538, 6148, 24584, 2943698366206691291790031665443150030830665744, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1086).pointIds 1086), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq6744 : B6744.tree = HexagonCover.NBand.M8300_8500.SplitData.node6744 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6743 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2854495385412568799223888792352556584806744080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B6744, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6743 : B6743.tree = HexagonCover.NBand.M8300_8500.SplitData.node6743 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6744
  · rfl
  · rfl

def B6742 : Block := .branch 161 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2854495385412568799223888792352556584806744080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6743, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq6742 : B6742.tree = HexagonCover.NBand.M8300_8500.SplitData.node6742 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6743
  · rfl
  · rfl
  · rfl
  · rfl

def B6741 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997892457936451903530140196872, 2854495385412568799223888792352556584806744080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6742, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq6741 : B6741.tree = HexagonCover.NBand.M8300_8500.SplitData.node6741 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6742
  · rfl
  · rfl
  · rfl

def B6740 : Block := .branch 168 ![57115266062853123556525597070983553, 146437906389534210, 4740813226943354771460, 664614077120620450716241123684147208, 2854495385412568799223888792352556584806744080, 393248, 3741444191567111470601433171753684530319737065308224] ![(.leaf 0 (Common.fact 1085).pointIds 1085), (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), B6741]
theorem treeEq6740 : B6740.tree = HexagonCover.NBand.M8300_8500.SplitData.node6740 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6741

def B6788 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 664614156348782964980578717228097544, 2854495385412893317777547219079339740827320336, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1141).pointIds 1141), (.leaf 4 (Common.fact 1142).pointIds 1142), (.leaf 5 (Common.fact 1124).pointIds 1124), (.leaf 6 (Common.fact 1132).pointIds 1132)]
theorem treeEq6788 : B6788.tree = HexagonCover.NBand.M8300_8500.SplitData.node6788 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6787 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 928455029610473112563877378, 4835703278458516698830852, 664614156348782964980578717228097544, 2854495385412893317777547219079339740827320336, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6788, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1129).pointIds 1129)]
theorem treeEq6787 : B6787.tree = HexagonCover.NBand.M8300_8500.SplitData.node6787 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6788
  · rfl
  · rfl
  · rfl
  · rfl

def B6786 : Block := .branch 168 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664614235576945479244916310772047880, 2854495385412893317777547219079339740827320336, 233845970963757826047978923686416002951423709282336, 3753136204665779961594995209069381255389949011165248] ![B6787, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1128).pointIds 1128)]
theorem treeEq6786 : B6786.tree = HexagonCover.NBand.M8300_8500.SplitData.node6786 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6787
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6785 : Block := .branch 163 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664614235576945479244916310772047880, 2854495385412893317777547219079339740827320336, 233845970963757826047978923686416002951423709282336, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1140).pointIds 1140), (.leaf 5 (Common.fact 329).pointIds 329), B6786]
theorem treeEq6785 : B6785.tree = HexagonCover.NBand.M8300_8500.SplitData.node6785 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6786

def B6784 : Block := .branch 165 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664614235576945479244916310772047880, 2854495385412893317777547219079339740827320336, 187077918569168932665461009039494946322433867907104, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1139).pointIds 1139), B6785, (.leaf 0 [] 0)]
theorem treeEq6784 : B6784.tree = HexagonCover.NBand.M8300_8500.SplitData.node6784 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6785
  · rfl

def B6783 : Block := .branch 167 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664614235576945479244916310772047880, 2854495385412893317777547219079339740827320336, 5708990813359135389350451810719806474502406176, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1138).pointIds 1138), B6784, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6783 : B6783.tree = HexagonCover.NBand.M8300_8500.SplitData.node6783 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6784
  · rfl

def B6745 : Block := .branch 108 ![46731939377413676886175963666186625, 928455029610473112563877378, 4840444091685460053596164, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), Tip6738_6746, B6783, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq6745 : B6745.tree = HexagonCover.NBand.M8300_8500.SplitData.node6745 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6783
  · rfl
  · rfl

def B6739 : Block := .branch 89 ![57116533094483332143236956324626817, 309485009967782975114315266, 4840444091685460053596164, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![B6740, B6745, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1084).pointIds 1084)]
theorem treeEq6739 : B6739.tree = HexagonCover.NBand.M8300_8500.SplitData.node6739 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6740
  · exact treeEq6745
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6793 : Block := .branch 163 ![385, 1538, 6148, 24584, 2943698366206691291790031665443150030830665744, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1086).pointIds 1086), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1146).pointIds 1146)]
theorem treeEq6793 : B6793.tree = HexagonCover.NBand.M8300_8500.SplitData.node6793 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6792 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2854495385412568799223888792352556584806744080, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B6793, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6792 : B6792.tree = HexagonCover.NBand.M8300_8500.SplitData.node6792 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6793
  · rfl
  · rfl

def B6791 : Block := .branch 161 ![385, 1538, 478734624567393153183651844, 1496577676626845252854571161159410264031205064204296, 2854495385412568799223888792352556584806744080, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1145).pointIds 1145), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B6792]
theorem treeEq6791 : B6791.tree = HexagonCover.NBand.M8300_8500.SplitData.node6791 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6792

def B6790 : Block := .branch 170 ![385, 146437906389534210, 478739365380620096538417156, 664613997892457936451903530140196872, 2854495385412568799223888792352556584806744080, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6791, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1144).pointIds 1144)]
theorem treeEq6790 : B6790.tree = HexagonCover.NBand.M8300_8500.SplitData.node6790 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6791
  · rfl
  · rfl
  · rfl

def B6789 : Block := .branch 160 ![385, 146437906389534210, 478739365380620096538417156, 664613997892457936451903530140196872, 2854495385412568799223888792352556584806744080, 393248, 748288838313443561768219193004703366977351702806592] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 1143).pointIds 1143), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B6790]
theorem treeEq6789 : B6789.tree = HexagonCover.NBand.M8300_8500.SplitData.node6789 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6790

def B6738 : Block := .branch 88 ![57116533094483332143236956324626817, 146437906389534210, 169254355559275027813636100, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 577).pointIds 577), B6739, B6789, (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1083).pointIds 1083)]
theorem treeEq6738 : B6738.tree = HexagonCover.NBand.M8300_8500.SplitData.node6738 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6739
  · exact treeEq6789
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6738 : B6738.accepted = true := by decide +kernel
theorem checked6738 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6738 (maskNeeds ![57116533094483332143236956324626817, 146437906389534210, 169254355559275027813636100, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136]) := by
  rw [← treeEq6738]
  exact B6738.sound accepted6738
#print axioms checked6738

def B6828 : Block := .branch 174 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 1496577676627525152974415145628400561342538460454920, 365464960762664228121581254401212924802696839184, 982129100286366761032876207585342189208786669273120, 14977468790561064383278418977075572393335922510790720] ![(.leaf 0 (Common.fact 1171).pointIds 1171), (.leaf 1 (Common.fact 1172).pointIds 1172), (.leaf 2 (Common.fact 1173).pointIds 1173), (.leaf 3 (Common.fact 1174).pointIds 1174), (.leaf 4 (Common.fact 1175).pointIds 1175), (.leaf 5 (Common.fact 1176).pointIds 1176), (.leaf 6 (Common.fact 1177).pointIds 1177)]
theorem treeEq6828 : B6828.tree = HexagonCover.NBand.M8300_8500.SplitData.node6828 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6829 : Block := .branch 174 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676627525152974415145628400561342538460454920, 365464960762664228121581254401212924802696839184, 982129100286366761032876207585342189208786669273120, 14980391793835726189114826346741004959375234375876672] ![(.leaf 0 (Common.fact 1171).pointIds 1171), (.leaf 1 (Common.fact 1172).pointIds 1172), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1174).pointIds 1174), (.leaf 4 (Common.fact 1175).pointIds 1175), (.leaf 5 (Common.fact 1176).pointIds 1176), (.leaf 6 (Common.fact 1179).pointIds 1179)]
theorem treeEq6829 : B6829.tree = HexagonCover.NBand.M8300_8500.SplitData.node6829 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6827 : Block := .branch 161 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676627525817588413038086337013246068600627208, 365464960762664228121581254401212924802696839184, 982129100286366761032876207585342189208786669273120, 14977468790561064383278418977075572393335922510790720] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6828, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B6829]
theorem treeEq6827 : B6827.tree = HexagonCover.NBand.M8300_8500.SplitData.node6827 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6828
  · rfl
  · rfl
  · rfl
  · exact treeEq6829

def B6830 : Block := .branch 174 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676627525152974415145628400561342538460454920, 2944046815350418332776618161041160161479196688, 795422266117343913232355470205837033447741286907936, 14977468790561064383278418977075572393335922510790720] ![(.leaf 0 (Common.fact 1171).pointIds 1171), (.leaf 1 (Common.fact 1172).pointIds 1172), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1174).pointIds 1174), (.leaf 4 (Common.fact 1180).pointIds 1180), (.leaf 5 (Common.fact 1181).pointIds 1181), (.leaf 6 (Common.fact 1177).pointIds 1177)]
theorem treeEq6830 : B6830.tree = HexagonCover.NBand.M8300_8500.SplitData.node6830 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6826 : Block := .branch 158 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676627525817588413038086337013246068600627208, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 14977468790561064383278418977075572393335922510790720] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), B6827, B6830, (.leaf 0 [] 0)]
theorem treeEq6826 : B6826.tree = HexagonCover.NBand.M8300_8500.SplitData.node6826 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6827
  · exact treeEq6830
  · rfl

def B6831 : Block := .branch 174 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676626845252854571161159410264031205064204296, 2943699046771425133666958592192364894367088656, 982129100286366761032876207585342189208786669273120, 14977468790561064383278418977075572393335922510790720] ![(.leaf 0 (Common.fact 1171).pointIds 1171), (.leaf 1 (Common.fact 1172).pointIds 1172), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1182).pointIds 1182), (.leaf 4 (Common.fact 1183).pointIds 1183), (.leaf 5 (Common.fact 1176).pointIds 1176), (.leaf 6 (Common.fact 1177).pointIds 1177)]
theorem treeEq6831 : B6831.tree = HexagonCover.NBand.M8300_8500.SplitData.node6831 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6825 : Block := .branch 129 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 14977468790582863722409291597391194829124520161837120] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), B6826, B6831, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1088).pointIds 1088)]
theorem treeEq6825 : B6825.tree = HexagonCover.NBand.M8300_8500.SplitData.node6825 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6826
  · exact treeEq6831
  · rfl
  · rfl

def B6824 : Block := .branch 173 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1168).pointIds 1168), (.leaf 4 (Common.fact 1169).pointIds 1169), (.leaf 5 (Common.fact 1170).pointIds 1170), B6825]
theorem treeEq6824 : B6824.tree = HexagonCover.NBand.M8300_8500.SplitData.node6824 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6825

def B6823 : Block := .branch 172 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![B6824, (.leaf 1 (Common.fact 1093).pointIds 1093), (.leaf 2 (Common.fact 1163).pointIds 1163), (.leaf 3 (Common.fact 1164).pointIds 1164), (.leaf 4 (Common.fact 1165).pointIds 1165), (.leaf 5 (Common.fact 1166).pointIds 1166), (.leaf 6 (Common.fact 1167).pointIds 1167)]
theorem treeEq6823 : B6823.tree = HexagonCover.NBand.M8300_8500.SplitData.node6823 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6824
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6822 : Block := .branch 88 ![374144419156711193792082694589045339207882397188481, 618970019644942487019062786, 1461501637330902918203689668419561478172631373828, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![(.leaf 0 (Common.fact 577).pointIds 577), B6823, (.leaf 2 (Common.fact 1161).pointIds 1161), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1162).pointIds 1162)]
theorem treeEq6822 : B6822.tree = HexagonCover.NBand.M8300_8500.SplitData.node6822 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6823
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6821 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 618970019789128043839096322, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6822, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1160).pointIds 1160)]
theorem treeEq6821 : B6821.tree = HexagonCover.NBand.M8300_8500.SplitData.node6821 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6822
  · rfl
  · rfl
  · rfl
  · rfl

def B6820 : Block := .branch 87 ![374144419156711193792082694589045339207882397188481, 618970019789128043839096322, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B6821, (.leaf 3 (Common.fact 1147).pointIds 1147), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 1159).pointIds 1159)]
theorem treeEq6820 : B6820.tree = HexagonCover.NBand.M8300_8500.SplitData.node6820 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6821
  · rfl
  · rfl
  · rfl
  · rfl

def B6819 : Block := .branch 89 ![374144419156711193792082694589045339207882397188481, 146437906389534210, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![(.leaf 0 (Common.fact 1148).pointIds 1148), B6820, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1158).pointIds 1158)]
theorem treeEq6819 : B6819.tree = HexagonCover.NBand.M8300_8500.SplitData.node6819 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6820
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6818 : Block := .branch 168 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 3004847377568107016484705447779404332103120769777728] ![B6819, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1157).pointIds 1157)]
theorem treeEq6818 : B6818.tree = HexagonCover.NBand.M8300_8500.SplitData.node6818 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6819
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6817 : Block := .branch 163 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 2944046815350418332776618161041160161479196688, 982129100286366761032876207585342189208786669273120, 2993155364469459793139075969117674067945873309433920] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), B6818]
theorem treeEq6817 : B6817.tree = HexagonCover.NBand.M8300_8500.SplitData.node6817 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6818

def B6816 : Block := .branch 151 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 2993155364469459793139075969117674067945873309433920] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6817, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1156).pointIds 1156)]
theorem treeEq6816 : B6816.tree = HexagonCover.NBand.M8300_8500.SplitData.node6816 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6817
  · rfl
  · rfl

def B6815 : Block := .branch 135 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 2993155364425903650173195845794362118194606978367552] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B6816]
theorem treeEq6815 : B6815.tree = HexagonCover.NBand.M8300_8500.SplitData.node6815 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6816

def B6814 : Block := .branch 169 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89551429938498570660046222142169888713703440, 233840261972944466912589573234605283144949207269408, 2993155364425903650173195845794362118194606978367552] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6815, (.leaf 6 (Common.fact 1155).pointIds 1155)]
theorem treeEq6814 : B6814.tree = HexagonCover.NBand.M8300_8500.SplitData.node6814 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6815
  · rfl

def B6813 : Block := .branch 86 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89551429938498570660046222142169888713703440, 233840261972944466912589573234605283144949207269408, 2993155364425903650173195845794362118194606978367552] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6814, (.leaf 3 (Common.fact 571).pointIds 571), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1154).pointIds 1154)]
theorem treeEq6813 : B6813.tree = HexagonCover.NBand.M8300_8500.SplitData.node6813 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6814
  · rfl
  · rfl
  · rfl
  · rfl

def B6812 : Block := .branch 138 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89202980794771529673459726544159758065172496, 233840261972944466912589573234605283144949207269408, 2993155364425908967085178985457853733422848099745856] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B6813, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6812 : B6812.tree = HexagonCover.NBand.M8300_8500.SplitData.node6812 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6813
  · rfl
  · rfl

theorem accepted6812 : B6812.accepted = true := by decide +kernel
theorem checked6812 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6812 (maskNeeds ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89202980794771529673459726544159758065172496, 233840261972944466912589573234605283144949207269408, 2993155364425908967085178985457853733422848099745856]) := by
  rw [← treeEq6812]
  exact B6812.sound accepted6812
#print axioms checked6812

def Tip6733_6738 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6738 ![57116533094483332143236956324626817, 146437906389534210, 169254355559275027813636100, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] checked6738
def B6800 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 664613998047200441362576064502587400, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1150).pointIds 1150), (.leaf 4 (Common.fact 1118).pointIds 1118), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6800 : B6800.tree = HexagonCover.NBand.M8300_8500.SplitData.node6800 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6799 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 928455029610473112563877378, 2923003274661805836407374501135844497828563916804, 664613998047200441362576064502587400, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6800, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1091).pointIds 1091)]
theorem treeEq6799 : B6799.tree = HexagonCover.NBand.M8300_8500.SplitData.node6799 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6800
  · rfl
  · rfl
  · rfl
  · rfl

def B6798 : Block := .branch 88 ![374144419156711193792082694589045339207882397188481, 618970019789128043839096322, 2923003274661805836407374501135844497828563916804, 664613998047200441362576064502587400, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 577).pointIds 577), B6799, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1083).pointIds 1083)]
theorem treeEq6798 : B6798.tree = HexagonCover.NBand.M8300_8500.SplitData.node6798 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6799
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6797 : Block := .branch 161 ![374144419156711193792082694589045339207882397188481, 618970019789128043839096322, 4835703278458516698830852, 664613998047200441362576064502587400, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6798, (.leaf 3 (Common.fact 1149).pointIds 1149), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1092).pointIds 1092)]
theorem treeEq6797 : B6797.tree = HexagonCover.NBand.M8300_8500.SplitData.node6797 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6798
  · rfl
  · rfl
  · rfl
  · rfl

def B6796 : Block := .branch 89 ![374144419156711193792082694589045339207882397188481, 146437906389534210, 4835703278458516698830852, 664613998047200441362576064502587400, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1148).pointIds 1148), B6797, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1084).pointIds 1084)]
theorem treeEq6796 : B6796.tree = HexagonCover.NBand.M8300_8500.SplitData.node6796 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6797
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6795 : Block := .branch 168 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 664614077275362955626913658046537736, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![B6796, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq6795 : B6795.tree = HexagonCover.NBand.M8300_8500.SplitData.node6795 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6796
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6794 : Block := .branch 170 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 664614077275362955626913658046537736, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 1147).pointIds 1147), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6795]
theorem treeEq6794 : B6794.tree = HexagonCover.NBand.M8300_8500.SplitData.node6794 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6795

def B6737 : Block := .branch 87 ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), Tip6733_6738, B6794, (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 1082).pointIds 1082)]
theorem treeEq6737 : B6737.tree = HexagonCover.NBand.M8300_8500.SplitData.node6737 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6794
  · rfl
  · rfl
  · rfl

def B6807 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 664613997969829188907239797321392136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1152).pointIds 1152), (.leaf 4 (Common.fact 1118).pointIds 1118), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6807 : B6807.tree = HexagonCover.NBand.M8300_8500.SplitData.node6807 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6806 : Block := .branch 160 ![374144419156711193792082694589045339207882397188481, 928455029610473112563877378, 2923003274661805836407374501135844497828563916804, 664613997969829188907239797321392136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6807, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1091).pointIds 1091)]
theorem treeEq6806 : B6806.tree = HexagonCover.NBand.M8300_8500.SplitData.node6806 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6807
  · rfl
  · rfl
  · rfl
  · rfl

def B6805 : Block := .branch 88 ![374144419156711193792082694589045339207882397188481, 618970019789128043839096322, 2923003274661805836407374501135844497828563916804, 664613997969829188907239797321392136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 577).pointIds 577), B6806, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1083).pointIds 1083)]
theorem treeEq6805 : B6805.tree = HexagonCover.NBand.M8300_8500.SplitData.node6805 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6806
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6804 : Block := .branch 161 ![374144419156711193792082694589045339207882397188481, 618970019789128043839096322, 4835703278458516698830852, 664613997969829188907239797321392136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6805, (.leaf 3 (Common.fact 1151).pointIds 1151), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1092).pointIds 1092)]
theorem treeEq6804 : B6804.tree = HexagonCover.NBand.M8300_8500.SplitData.node6804 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6805
  · rfl
  · rfl
  · rfl
  · rfl

def B6803 : Block := .branch 89 ![374144419156711193792082694589045339207882397188481, 146437906389534210, 4835703278458516698830852, 664613997969829188907239797321392136, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1148).pointIds 1148), B6804, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1084).pointIds 1084)]
theorem treeEq6803 : B6803.tree = HexagonCover.NBand.M8300_8500.SplitData.node6803 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6804
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6802 : Block := .branch 168 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 664614077197991703171577390865342472, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![B6803, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq6802 : B6802.tree = HexagonCover.NBand.M8300_8500.SplitData.node6802 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6803
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6801 : Block := .branch 170 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 664614077197991703171577390865342472, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444191567132738249365730407650991232701550821440] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 571).pointIds 571), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6802]
theorem treeEq6801 : B6801.tree = HexagonCover.NBand.M8300_8500.SplitData.node6801 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6802

def B6736 : Block := .branch 86 ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6737, B6801, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1081).pointIds 1081)]
theorem treeEq6736 : B6736.tree = HexagonCover.NBand.M8300_8500.SplitData.node6736 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6737
  · exact treeEq6801
  · rfl
  · rfl
  · rfl

def B6735 : Block := .branch 151 ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 649037107316853453566312041250832, 5708990813359135389350451810719806474502406176, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6736, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1080).pointIds 1080)]
theorem treeEq6735 : B6735.tree = HexagonCover.NBand.M8300_8500.SplitData.node6735 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6736
  · rfl
  · rfl

def B6734 : Block := .branch 152 ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 649037107316853453566312041250832, 42535295865117307932921825928971419680, 3741444202739288725909600502500657717660756590723136] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B6735, (.leaf 6 (Common.fact 1079).pointIds 1079)]
theorem treeEq6734 : B6734.tree = HexagonCover.NBand.M8300_8500.SplitData.node6734 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6735
  · rfl

def B6733 : Block := .branch 169 ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 649037107316853453566312041250832, 42535295865117307932921825928971419680, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 540).pointIds 540), B6734]
theorem treeEq6733 : B6733.tree = HexagonCover.NBand.M8300_8500.SplitData.node6733 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6734

theorem accepted6733 : B6733.accepted = true := by decide +kernel
theorem checked6733 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6733 (maskNeeds ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 649037107316853453566312041250832, 42535295865117307932921825928971419680, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6733]
  exact B6733.sound accepted6733
#print axioms checked6733

end HexagonCover.NBand.M8300_8500.SplitTree.Run0093
