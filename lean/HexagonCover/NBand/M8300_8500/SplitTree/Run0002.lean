import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B0206 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604374259524338235809165892803314950078528] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 598).pointIds 598)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M8300_8500.SplitData.node0206 := by
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

def B0205 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604374259524338235809165892803314950078528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0206, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M8300_8500.SplitData.node0205 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · rfl

def B0204 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 89551429938498570660046222142169888713703440, 393248, 374144430350685083043191698406218268547965102063680] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 562).pointIds 562), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 563).pointIds 563), B0205]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M8300_8500.SplitData.node0204 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0205

def B0203 : Block := .branch 125 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 89551429938498570660046222142169888713703440, 748288838313422294120286634350736906063837462396960, 374144430350642547747326581098285346722036131037248] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), B0204]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M8300_8500.SplitData.node0203 := by
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
  · exact treeEq0204

def B0202 : Block := .branch 86 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551429938498570660046222142169888713703440, 748288838313422294120286634350736906063837462396960, 374144430350642547747326581098285346722036131037248] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0203, (.leaf 3 (Common.fact 571).pointIds 571), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M8300_8500.SplitData.node0202 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0203
  · rfl
  · rfl
  · rfl
  · rfl

def B0201 : Block := .branch 138 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 748288838313422294120286634350736906063837462396960, 374144430372447203790182341077399397738874903461952] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0202, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M8300_8500.SplitData.node0201 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl
  · rfl

def B0200 : Block := .branch 165 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 748288838313422294120286634350736906063837462396960, 374144430372447203790182341077399397738874903461952] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0201, (.leaf 0 [] 0)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M8300_8500.SplitData.node0200 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201
  · rfl

def B0199 : Block := .branch 167 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 748288838313422294120286634350736906063837462396960, 374144430372447203790182341077399397738874903461952] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0200, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M8300_8500.SplitData.node0199 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl

def B0198 : Block := .branch 146 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 374144430372447203790182341077399397738874903461952] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0199, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M8300_8500.SplitData.node0198 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl

def B0197 : Block := .branch 170 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 374144430372447203790182341077399397738874903461952] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0198, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M8300_8500.SplitData.node0197 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0198
  · rfl
  · rfl
  · rfl

def B0196 : Block := .branch 135 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 374144430328891060824302217754087447987608572395584] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B0197]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M8300_8500.SplitData.node0196 := by
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
  · exact treeEq0197

def B0195 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 374144430328891060824302217754087447987608572395584] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 587).pointIds 587), B0196, (.leaf 6 (Common.fact 588).pointIds 588)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M8300_8500.SplitData.node0195 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl

def B0194 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 11172179913764158900578718994955689841393728] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 555).pointIds 555), (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 561).pointIds 561), B0195]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M8300_8500.SplitData.node0194 := by
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
  · exact treeEq0195

theorem accepted0194 : B0194.accepted = true := by decide +kernel
theorem checked0194 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0194 (maskNeeds ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 11172179913764158900578718994955689841393728]) := by
  rw [← treeEq0194]
  exact B0194.sound accepted0194
#print axioms checked0194

def B0243 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M8300_8500.SplitData.node0243 := by
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

def B0242 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0243, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M8300_8500.SplitData.node0242 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0243
  · rfl
  · rfl

def B0241 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B0242, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M8300_8500.SplitData.node0241 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0242
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0240 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0241, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M8300_8500.SplitData.node0240 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0241
  · rfl
  · rfl
  · rfl
  · rfl

def B0239 : Block := .branch 166 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783604371601068346665977420085189194389389376] ![B0240, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M8300_8500.SplitData.node0239 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0240
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0238 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 625).pointIds 625), B0239]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M8300_8500.SplitData.node0238 := by
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
  · exact treeEq0239

def B0237 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551429938498570660046222142169888713703440, 233840261972944508450964441513226311388919841030176, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0238, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M8300_8500.SplitData.node0237 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238
  · rfl

def B0236 : Block := .branch 138 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 233840261972944508450964441513226311388919841030176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0237, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M8300_8500.SplitData.node0236 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0237
  · rfl
  · rfl

def B0235 : Block := .branch 165 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 187072209578355615068446526866305254759929999654944, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0236, (.leaf 0 [] 0)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M8300_8500.SplitData.node0235 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl

def B0234 : Block := .branch 167 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0235, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M8300_8500.SplitData.node0234 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0235
  · rfl

def B0233 : Block := .branch 146 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0234, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M8300_8500.SplitData.node0233 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl
  · rfl

def B0232 : Block := .branch 170 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 619).pointIds 619), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0233, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 620).pointIds 620), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M8300_8500.SplitData.node0232 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0233
  · rfl
  · rfl
  · rfl

theorem accepted0232 : B0232.accepted = true := by decide +kernel
theorem checked0232 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0232 (maskNeeds ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq0232]
  exact B0232.sound accepted0232
#print axioms checked0232

def B0255 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M8300_8500.SplitData.node0255 := by
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

def B0254 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0255, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M8300_8500.SplitData.node0254 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0255
  · rfl
  · rfl

def B0253 : Block := .branch 166 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B0254, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M8300_8500.SplitData.node0253 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0254
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0252 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0253, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M8300_8500.SplitData.node0252 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0253
  · rfl
  · rfl

def B0251 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0252, (.leaf 0 [] 0)]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M8300_8500.SplitData.node0251 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0252
  · rfl

def B0250 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0251, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M8300_8500.SplitData.node0250 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0251
  · rfl

def B0249 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0250, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M8300_8500.SplitData.node0249 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0250
  · rfl
  · rfl

def B0248 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 577).pointIds 577), B0249, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M8300_8500.SplitData.node0248 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0249
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0247 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0248, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M8300_8500.SplitData.node0247 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0248
  · rfl
  · rfl
  · rfl
  · rfl

def B0246 : Block := .branch 170 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 619).pointIds 619), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0247, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 620).pointIds 620), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M8300_8500.SplitData.node0246 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · rfl
  · rfl
  · rfl

def B0245 : Block := .branch 135 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B0246]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M8300_8500.SplitData.node0245 := by
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
  · exact treeEq0246

def B0244 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0245, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M8300_8500.SplitData.node0244 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl

theorem accepted0244 : B0244.accepted = true := by decide +kernel
theorem checked0244 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0244 (maskNeeds ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432]) := by
  rw [← treeEq0244]
  exact B0244.sound accepted0244
#print axioms checked0244

def Tip0219_0232 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0232 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] checked0232
def Tip0219_0244 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0244 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] checked0244
def B0231 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M8300_8500.SplitData.node0231 := by
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

def B0230 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0231, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M8300_8500.SplitData.node0230 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231
  · rfl
  · rfl

def B0229 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0230, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M8300_8500.SplitData.node0229 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl

def B0228 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0229, (.leaf 0 [] 0)]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M8300_8500.SplitData.node0228 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0229
  · rfl

def B0227 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0228, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M8300_8500.SplitData.node0227 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl

def B0226 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0227, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M8300_8500.SplitData.node0226 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0227
  · rfl
  · rfl

def B0225 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B0226, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M8300_8500.SplitData.node0225 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0224 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0225, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M8300_8500.SplitData.node0224 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0225
  · rfl
  · rfl
  · rfl
  · rfl

def B0223 : Block := .branch 170 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 619).pointIds 619), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0224, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 620).pointIds 620), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M8300_8500.SplitData.node0223 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · rfl
  · rfl
  · rfl

def B0222 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 618).pointIds 618), B0223]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M8300_8500.SplitData.node0222 := by
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
  · exact treeEq0223

def B0221 : Block := .branch 125 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0222, Tip0219_0232]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M8300_8500.SplitData.node0221 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0222
  · rfl

def B0220 : Block := .branch 121 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0221, (.leaf 5 (Common.fact 256).pointIds 256), Tip0219_0244]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M8300_8500.SplitData.node0220 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0221
  · rfl
  · rfl

def B0260 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M8300_8500.SplitData.node0260 := by
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

def B0259 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0260, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M8300_8500.SplitData.node0259 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0260
  · rfl

def B0258 : Block := .branch 163 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0259]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M8300_8500.SplitData.node0258 := by
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
  · exact treeEq0259

def B0257 : Block := .branch 165 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0258, (.leaf 0 [] 0)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M8300_8500.SplitData.node0257 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258
  · rfl

def B0256 : Block := .branch 167 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0257, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M8300_8500.SplitData.node0256 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0257
  · rfl

def B0219 : Block := .branch 119 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0220, B0256, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M8300_8500.SplitData.node0219 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0220
  · exact treeEq0256
  · rfl
  · rfl

theorem accepted0219 : B0219.accepted = true := by decide +kernel
theorem checked0219 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0219 (maskNeeds ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0219]
  exact B0219.sound accepted0219
#print axioms checked0219

def Tip0214_0219 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0219 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] checked0219
def B0265 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M8300_8500.SplitData.node0265 := by
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

def B0264 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0265, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M8300_8500.SplitData.node0264 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0265
  · rfl

def B0263 : Block := .branch 163 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B0264]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M8300_8500.SplitData.node0263 := by
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
  · exact treeEq0264

def B0262 : Block := .branch 165 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B0263, (.leaf 0 [] 0)]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M8300_8500.SplitData.node0262 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0263
  · rfl

def B0261 : Block := .branch 167 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B0262, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M8300_8500.SplitData.node0261 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0262
  · rfl

def B0218 : Block := .branch 108 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), Tip0214_0219, B0261, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M8300_8500.SplitData.node0218 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0261
  · rfl
  · rfl

def B0270 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M8300_8500.SplitData.node0270 := by
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

def B0269 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0270, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M8300_8500.SplitData.node0269 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0270
  · rfl

def B0268 : Block := .branch 163 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B0269]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M8300_8500.SplitData.node0268 := by
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
  · exact treeEq0269

def B0267 : Block := .branch 165 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B0268, (.leaf 0 [] 0)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M8300_8500.SplitData.node0267 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0268
  · rfl

def B0266 : Block := .branch 167 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B0267, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M8300_8500.SplitData.node0266 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0267
  · rfl

def B0217 : Block := .branch 98 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0218, B0266, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M8300_8500.SplitData.node0217 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0218
  · exact treeEq0266
  · rfl
  · rfl

def B0273 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M8300_8500.SplitData.node0273 := by
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

def B0272 : Block := .branch 169 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0273, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M8300_8500.SplitData.node0272 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0273
  · rfl

def B0271 : Block := .branch 170 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158533696280984011454269120520, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 619).pointIds 619), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 620).pointIds 620), B0272]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M8300_8500.SplitData.node0271 := by
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
  · exact treeEq0272

def B0216 : Block := .branch 86 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0217, B0271, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M8300_8500.SplitData.node0216 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0217
  · exact treeEq0271
  · rfl
  · rfl
  · rfl

def B0215 : Block := .branch 171 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 613).pointIds 613), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 614).pointIds 614), B0216]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M8300_8500.SplitData.node0215 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216

def B0214 : Block := .branch 168 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 611).pointIds 611), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 612).pointIds 612), B0215]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M8300_8500.SplitData.node0214 := by
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
  · exact treeEq0215

theorem accepted0214 : B0214.accepted = true := by decide +kernel
theorem checked0214 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0214 (maskNeeds ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 11172177255308167330746973187341569280704576]) := by
  rw [← treeEq0214]
  exact B0214.sound accepted0214
#print axioms checked0214

end HexagonCover.NBand.M8300_8500.SplitTree.Run0002
