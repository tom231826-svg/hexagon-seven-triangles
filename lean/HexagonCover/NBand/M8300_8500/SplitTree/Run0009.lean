import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0008
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0009
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B0769 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0769 : B0769.tree = HexagonCover.NBand.M8300_8500.SplitData.node0769 := by
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

def B0768 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0769, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0768 : B0768.tree = HexagonCover.NBand.M8300_8500.SplitData.node0768 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0769
  · rfl
  · rfl

def B0767 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B0768, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0767 : B0767.tree = HexagonCover.NBand.M8300_8500.SplitData.node0767 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0768
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0766 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0767, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0766 : B0766.tree = HexagonCover.NBand.M8300_8500.SplitData.node0766 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0767
  · rfl
  · rfl
  · rfl
  · rfl

def B0765 : Block := .branch 166 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783604371601068346665977420085189194389389376] ![B0766, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0765 : B0765.tree = HexagonCover.NBand.M8300_8500.SplitData.node0765 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0766
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0764 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 625).pointIds 625), B0765]
theorem treeEq0764 : B0764.tree = HexagonCover.NBand.M8300_8500.SplitData.node0764 := by
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
  · exact treeEq0765

def B0763 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551429938498570660046222142169888713703440, 233840261972944508450964441513226311388919841030176, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0764, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0763 : B0763.tree = HexagonCover.NBand.M8300_8500.SplitData.node0763 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0764
  · rfl

def B0762 : Block := .branch 138 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 233840261972944508450964441513226311388919841030176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0763, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0762 : B0762.tree = HexagonCover.NBand.M8300_8500.SplitData.node0762 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0763
  · rfl
  · rfl

def B0761 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 187072209578355615068446526866305254759929999654944, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0762, (.leaf 0 [] 0)]
theorem treeEq0761 : B0761.tree = HexagonCover.NBand.M8300_8500.SplitData.node0761 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0762
  · rfl

def B0760 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0761, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0760 : B0760.tree = HexagonCover.NBand.M8300_8500.SplitData.node0760 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0761
  · rfl

def B0759 : Block := .branch 146 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0760, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0759 : B0759.tree = HexagonCover.NBand.M8300_8500.SplitData.node0759 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0760
  · rfl
  · rfl

def B0758 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0759, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0758 : B0758.tree = HexagonCover.NBand.M8300_8500.SplitData.node0758 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0759
  · rfl
  · rfl
  · rfl

theorem accepted0758 : B0758.accepted = true := by decide +kernel
theorem checked0758 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0758 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq0758]
  exact B0758.sound accepted0758
#print axioms checked0758

def B0781 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0781 : B0781.tree = HexagonCover.NBand.M8300_8500.SplitData.node0781 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0780 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0781, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0780 : B0780.tree = HexagonCover.NBand.M8300_8500.SplitData.node0780 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0781
  · rfl
  · rfl

def B0779 : Block := .branch 166 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B0780, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0779 : B0779.tree = HexagonCover.NBand.M8300_8500.SplitData.node0779 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0780
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0778 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0779, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0778 : B0778.tree = HexagonCover.NBand.M8300_8500.SplitData.node0778 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0779
  · rfl
  · rfl

def B0777 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0778, (.leaf 0 [] 0)]
theorem treeEq0777 : B0777.tree = HexagonCover.NBand.M8300_8500.SplitData.node0777 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0778
  · rfl

def B0776 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0777, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0776 : B0776.tree = HexagonCover.NBand.M8300_8500.SplitData.node0776 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0777
  · rfl

def B0775 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0776, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0775 : B0775.tree = HexagonCover.NBand.M8300_8500.SplitData.node0775 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0776
  · rfl
  · rfl

def B0774 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 577).pointIds 577), B0775, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0774 : B0774.tree = HexagonCover.NBand.M8300_8500.SplitData.node0774 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0775
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0773 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0774, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0773 : B0773.tree = HexagonCover.NBand.M8300_8500.SplitData.node0773 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0774
  · rfl
  · rfl
  · rfl
  · rfl

def B0772 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0773, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0772 : B0772.tree = HexagonCover.NBand.M8300_8500.SplitData.node0772 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0773
  · rfl
  · rfl
  · rfl

def B0771 : Block := .branch 135 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B0772]
theorem treeEq0771 : B0771.tree = HexagonCover.NBand.M8300_8500.SplitData.node0771 := by
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
  · exact treeEq0772

def B0770 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0771, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0770 : B0770.tree = HexagonCover.NBand.M8300_8500.SplitData.node0770 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0771
  · rfl

theorem accepted0770 : B0770.accepted = true := by decide +kernel
theorem checked0770 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0770 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432]) := by
  rw [← treeEq0770]
  exact B0770.sound accepted0770
#print axioms checked0770

def Tip0705_0707 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0707 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0008.checked0707
def B0739 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0739 : B0739.tree = HexagonCover.NBand.M8300_8500.SplitData.node0739 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0738 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0739, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0738 : B0738.tree = HexagonCover.NBand.M8300_8500.SplitData.node0738 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0739
  · rfl
  · rfl

def B0737 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0738, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0737 : B0737.tree = HexagonCover.NBand.M8300_8500.SplitData.node0737 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0738
  · rfl
  · rfl

def B0736 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0737, (.leaf 0 [] 0)]
theorem treeEq0736 : B0736.tree = HexagonCover.NBand.M8300_8500.SplitData.node0736 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0737
  · rfl

def B0735 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0736, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0735 : B0735.tree = HexagonCover.NBand.M8300_8500.SplitData.node0735 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0736
  · rfl

def B0734 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0735, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0734 : B0734.tree = HexagonCover.NBand.M8300_8500.SplitData.node0734 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0735
  · rfl
  · rfl

def B0733 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 577).pointIds 577), B0734, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0733 : B0733.tree = HexagonCover.NBand.M8300_8500.SplitData.node0733 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0734
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0732 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0733, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0732 : B0732.tree = HexagonCover.NBand.M8300_8500.SplitData.node0732 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0733
  · rfl
  · rfl
  · rfl
  · rfl

def B0731 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0732, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0731 : B0731.tree = HexagonCover.NBand.M8300_8500.SplitData.node0731 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0732
  · rfl
  · rfl
  · rfl

def B0730 : Block := .branch 135 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B0731]
theorem treeEq0730 : B0730.tree = HexagonCover.NBand.M8300_8500.SplitData.node0730 := by
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
  · exact treeEq0731

def B0729 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0730, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0729 : B0729.tree = HexagonCover.NBand.M8300_8500.SplitData.node0729 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0730
  · rfl

def B0706 : Block := .branch 121 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip0705_0707, (.leaf 5 (Common.fact 256).pointIds 256), B0729]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M8300_8500.SplitData.node0706 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0729

def B0744 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0744 : B0744.tree = HexagonCover.NBand.M8300_8500.SplitData.node0744 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0743 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0744, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0743 : B0743.tree = HexagonCover.NBand.M8300_8500.SplitData.node0743 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0744
  · rfl

def B0742 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0743]
theorem treeEq0742 : B0742.tree = HexagonCover.NBand.M8300_8500.SplitData.node0742 := by
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
  · exact treeEq0743

def B0741 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0742, (.leaf 0 [] 0)]
theorem treeEq0741 : B0741.tree = HexagonCover.NBand.M8300_8500.SplitData.node0741 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0742
  · rfl

def B0740 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0741, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0740 : B0740.tree = HexagonCover.NBand.M8300_8500.SplitData.node0740 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0741
  · rfl

def B0705 : Block := .branch 119 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0706, B0740, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M8300_8500.SplitData.node0705 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0706
  · exact treeEq0740
  · rfl
  · rfl

theorem accepted0705 : B0705.accepted = true := by decide +kernel
theorem checked0705 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0705 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0705]
  exact B0705.sound accepted0705
#print axioms checked0705

def Tip0704_0758 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0758 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] checked0758
def Tip0704_0770 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0770 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] checked0770
def Tip0704_0705 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0705 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0705
def B0757 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq0757 : B0757.tree = HexagonCover.NBand.M8300_8500.SplitData.node0757 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0756 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0757, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0756 : B0756.tree = HexagonCover.NBand.M8300_8500.SplitData.node0756 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0757
  · rfl
  · rfl

def B0755 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0756, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0755 : B0755.tree = HexagonCover.NBand.M8300_8500.SplitData.node0755 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0756
  · rfl
  · rfl

def B0754 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0755, (.leaf 0 [] 0)]
theorem treeEq0754 : B0754.tree = HexagonCover.NBand.M8300_8500.SplitData.node0754 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0755
  · rfl

def B0753 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0754, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0753 : B0753.tree = HexagonCover.NBand.M8300_8500.SplitData.node0753 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0754
  · rfl

def B0752 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0753, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0752 : B0752.tree = HexagonCover.NBand.M8300_8500.SplitData.node0752 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0753
  · rfl
  · rfl

def B0751 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B0752, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0751 : B0751.tree = HexagonCover.NBand.M8300_8500.SplitData.node0751 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0752
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0750 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0751, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0750 : B0750.tree = HexagonCover.NBand.M8300_8500.SplitData.node0750 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0751
  · rfl
  · rfl
  · rfl
  · rfl

def B0749 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0750, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0749 : B0749.tree = HexagonCover.NBand.M8300_8500.SplitData.node0749 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0750
  · rfl
  · rfl
  · rfl

def B0748 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 618).pointIds 618), B0749]
theorem treeEq0748 : B0748.tree = HexagonCover.NBand.M8300_8500.SplitData.node0748 := by
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
  · exact treeEq0749

def B0747 : Block := .branch 125 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0748, Tip0704_0758]
theorem treeEq0747 : B0747.tree = HexagonCover.NBand.M8300_8500.SplitData.node0747 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0748
  · rfl

def B0746 : Block := .branch 121 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0747, (.leaf 5 (Common.fact 256).pointIds 256), Tip0704_0770]
theorem treeEq0746 : B0746.tree = HexagonCover.NBand.M8300_8500.SplitData.node0746 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0747
  · rfl
  · rfl

def B0786 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0786 : B0786.tree = HexagonCover.NBand.M8300_8500.SplitData.node0786 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0785 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0786, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0785 : B0785.tree = HexagonCover.NBand.M8300_8500.SplitData.node0785 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0786
  · rfl

def B0784 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0785]
theorem treeEq0784 : B0784.tree = HexagonCover.NBand.M8300_8500.SplitData.node0784 := by
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
  · exact treeEq0785

def B0783 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0784, (.leaf 0 [] 0)]
theorem treeEq0783 : B0783.tree = HexagonCover.NBand.M8300_8500.SplitData.node0783 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0784
  · rfl

def B0782 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0783, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0782 : B0782.tree = HexagonCover.NBand.M8300_8500.SplitData.node0782 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0783
  · rfl

def B0745 : Block := .branch 119 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0746, B0782, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0745 : B0745.tree = HexagonCover.NBand.M8300_8500.SplitData.node0745 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0746
  · exact treeEq0782
  · rfl
  · rfl

def B0704 : Block := .branch 115 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0704_0705, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B0745, (.leaf 0 [] 0)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M8300_8500.SplitData.node0704 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0745
  · rfl

theorem accepted0704 : B0704.accepted = true := by decide +kernel
theorem checked0704 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0704 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0704]
  exact B0704.sound accepted0704
#print axioms checked0704

def Tip0702_0704 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0704 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0704
def B0797 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0797 : B0797.tree = HexagonCover.NBand.M8300_8500.SplitData.node0797 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0796 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0797, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0796 : B0796.tree = HexagonCover.NBand.M8300_8500.SplitData.node0796 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0797
  · rfl
  · rfl

def B0795 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0796, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0795 : B0795.tree = HexagonCover.NBand.M8300_8500.SplitData.node0795 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0796
  · rfl
  · rfl

def B0794 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0795, (.leaf 0 [] 0)]
theorem treeEq0794 : B0794.tree = HexagonCover.NBand.M8300_8500.SplitData.node0794 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0795
  · rfl

def B0793 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0794, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0793 : B0793.tree = HexagonCover.NBand.M8300_8500.SplitData.node0793 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0794
  · rfl

def B0792 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0793, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0792 : B0792.tree = HexagonCover.NBand.M8300_8500.SplitData.node0792 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0793
  · rfl
  · rfl

def B0791 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 577).pointIds 577), B0792, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0791 : B0791.tree = HexagonCover.NBand.M8300_8500.SplitData.node0791 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0792
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0790 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0791, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0790 : B0790.tree = HexagonCover.NBand.M8300_8500.SplitData.node0790 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0791
  · rfl
  · rfl
  · rfl
  · rfl

def B0789 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 24584, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0790, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0789 : B0789.tree = HexagonCover.NBand.M8300_8500.SplitData.node0789 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0790
  · rfl
  · rfl
  · rfl

def B0788 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B0789]
theorem treeEq0788 : B0788.tree = HexagonCover.NBand.M8300_8500.SplitData.node0788 := by
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
  · exact treeEq0789

def B0787 : Block := .branch 135 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0788, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0787 : B0787.tree = HexagonCover.NBand.M8300_8500.SplitData.node0787 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0788
  · rfl

def B0703 : Block := .branch 113 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0702_0704, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B0787]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M8300_8500.SplitData.node0703 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0787

def B0802 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0802 : B0802.tree = HexagonCover.NBand.M8300_8500.SplitData.node0802 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0801 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0802, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0801 : B0801.tree = HexagonCover.NBand.M8300_8500.SplitData.node0801 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0802
  · rfl

def B0800 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B0801]
theorem treeEq0800 : B0800.tree = HexagonCover.NBand.M8300_8500.SplitData.node0800 := by
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
  · exact treeEq0801

def B0799 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B0800, (.leaf 0 [] 0)]
theorem treeEq0799 : B0799.tree = HexagonCover.NBand.M8300_8500.SplitData.node0799 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0800
  · rfl

def B0798 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B0799, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0798 : B0798.tree = HexagonCover.NBand.M8300_8500.SplitData.node0798 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0799
  · rfl

def B0702 : Block := .branch 108 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0703, B0798, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M8300_8500.SplitData.node0702 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0703
  · exact treeEq0798
  · rfl
  · rfl

theorem accepted0702 : B0702.accepted = true := by decide +kernel
theorem checked0702 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0702 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0702]
  exact B0702.sound accepted0702
#print axioms checked0702

end HexagonCover.NBand.M8300_8500.SplitTree.Run0009
