import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0058
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0059
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip4257_4258 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4258 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0058.checked4258
def B4282 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4282 : B4282.tree = HexagonCover.NBand.M8300_8500.SplitData.node4282 := by
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
  · rfl

def B4281 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4282, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4281 : B4281.tree = HexagonCover.NBand.M8300_8500.SplitData.node4281 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4282
  · rfl
  · rfl
  · rfl

def B4280 : Block := .branch 169 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B4281]
theorem treeEq4280 : B4280.tree = HexagonCover.NBand.M8300_8500.SplitData.node4280 := by
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
  · exact treeEq4281

def B4286 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4286 : B4286.tree = HexagonCover.NBand.M8300_8500.SplitData.node4286 := by
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
  · rfl

def B4285 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4286, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4285 : B4285.tree = HexagonCover.NBand.M8300_8500.SplitData.node4285 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4286
  · rfl

def B4284 : Block := .branch 161 ![2251799813685633, 360358888689632770, 113336831617668504098820, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4285]
theorem treeEq4284 : B4284.tree = HexagonCover.NBand.M8300_8500.SplitData.node4284 := by
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
  · exact treeEq4285

def B4283 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4284, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4283 : B4283.tree = HexagonCover.NBand.M8300_8500.SplitData.node4283 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4284
  · rfl
  · rfl
  · rfl

def B4279 : Block := .branch 125 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4280, B4283]
theorem treeEq4279 : B4279.tree = HexagonCover.NBand.M8300_8500.SplitData.node4279 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4280
  · exact treeEq4283

def B4290 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4290 : B4290.tree = HexagonCover.NBand.M8300_8500.SplitData.node4290 := by
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
  · rfl

def B4289 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4290, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4289 : B4289.tree = HexagonCover.NBand.M8300_8500.SplitData.node4289 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4290
  · rfl
  · rfl
  · rfl

def B4288 : Block := .branch 135 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B4289]
theorem treeEq4288 : B4288.tree = HexagonCover.NBand.M8300_8500.SplitData.node4288 := by
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
  · exact treeEq4289

def B4287 : Block := .branch 169 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4288, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4287 : B4287.tree = HexagonCover.NBand.M8300_8500.SplitData.node4287 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4288
  · rfl

def B4278 : Block := .branch 121 ![2251799813685633, 360358888689632770, 113336831617668504098820, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B4279, (.leaf 5 (Common.fact 256).pointIds 256), B4287]
theorem treeEq4278 : B4278.tree = HexagonCover.NBand.M8300_8500.SplitData.node4278 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4279
  · rfl
  · exact treeEq4287

def B4295 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4295 : B4295.tree = HexagonCover.NBand.M8300_8500.SplitData.node4295 := by
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

def B4294 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4295, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4294 : B4294.tree = HexagonCover.NBand.M8300_8500.SplitData.node4294 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4295
  · rfl

def B4293 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4294]
theorem treeEq4293 : B4293.tree = HexagonCover.NBand.M8300_8500.SplitData.node4293 := by
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
  · exact treeEq4294

def B4292 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4293, (.leaf 0 [] 0)]
theorem treeEq4292 : B4292.tree = HexagonCover.NBand.M8300_8500.SplitData.node4292 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4293
  · rfl

def B4291 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4292, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4291 : B4291.tree = HexagonCover.NBand.M8300_8500.SplitData.node4291 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4292
  · rfl

def B4277 : Block := .branch 119 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4278, B4291, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4277 : B4277.tree = HexagonCover.NBand.M8300_8500.SplitData.node4277 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4278
  · exact treeEq4291
  · rfl
  · rfl

def B4257 : Block := .branch 115 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4257_4258, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B4277, (.leaf 0 [] 0)]
theorem treeEq4257 : B4257.tree = HexagonCover.NBand.M8300_8500.SplitData.node4257 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4277
  · rfl

theorem accepted4257 : B4257.accepted = true := by decide +kernel
theorem checked4257 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4257 (maskNeeds ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4257]
  exact B4257.sound accepted4257
#print axioms checked4257

def Tip4254_4257 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4257 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4257
def B4299 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq4299 : B4299.tree = HexagonCover.NBand.M8300_8500.SplitData.node4299 := by
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
  · rfl

def B4298 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4299, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq4298 : B4298.tree = HexagonCover.NBand.M8300_8500.SplitData.node4298 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4299
  · rfl
  · rfl
  · rfl

def B4297 : Block := .branch 169 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400333925883571647971334348810992746560] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4298]
theorem treeEq4297 : B4297.tree = HexagonCover.NBand.M8300_8500.SplitData.node4297 := by
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
  · exact treeEq4298

def B4296 : Block := .branch 135 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772933191195142415830470672991745736768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4297, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq4296 : B4296.tree = HexagonCover.NBand.M8300_8500.SplitData.node4296 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4297
  · rfl

def B4256 : Block := .branch 113 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4254_4257, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B4296]
theorem treeEq4256 : B4256.tree = HexagonCover.NBand.M8300_8500.SplitData.node4256 := by
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
  · exact treeEq4296

def B4304 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4304 : B4304.tree = HexagonCover.NBand.M8300_8500.SplitData.node4304 := by
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

def B4303 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4304, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4303 : B4303.tree = HexagonCover.NBand.M8300_8500.SplitData.node4303 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4304
  · rfl

def B4302 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B4303]
theorem treeEq4302 : B4302.tree = HexagonCover.NBand.M8300_8500.SplitData.node4302 := by
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
  · exact treeEq4303

def B4301 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B4302, (.leaf 0 [] 0)]
theorem treeEq4301 : B4301.tree = HexagonCover.NBand.M8300_8500.SplitData.node4301 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4302
  · rfl

def B4300 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B4301, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4300 : B4300.tree = HexagonCover.NBand.M8300_8500.SplitData.node4300 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4301
  · rfl

def B4255 : Block := .branch 108 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B4256, B4300, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq4255 : B4255.tree = HexagonCover.NBand.M8300_8500.SplitData.node4255 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4256
  · exact treeEq4300
  · rfl
  · rfl

def B4308 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq4308 : B4308.tree = HexagonCover.NBand.M8300_8500.SplitData.node4308 := by
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
  · rfl

def B4307 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4308, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq4307 : B4307.tree = HexagonCover.NBand.M8300_8500.SplitData.node4307 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4308
  · rfl
  · rfl
  · rfl

def B4306 : Block := .branch 169 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400323542557505178544306689315037511744] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4307]
theorem treeEq4306 : B4306.tree = HexagonCover.NBand.M8300_8500.SplitData.node4306 := by
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
  · exact treeEq4307

def B4305 : Block := .branch 135 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922807869075946403443013495790501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4306, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4305 : B4305.tree = HexagonCover.NBand.M8300_8500.SplitData.node4305 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4306
  · rfl

def B4254 : Block := .branch 100 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B4255, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B4305]
theorem treeEq4254 : B4254.tree = HexagonCover.NBand.M8300_8500.SplitData.node4254 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4255
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4305

theorem accepted4254 : B4254.accepted = true := by decide +kernel
theorem checked4254 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4254 (maskNeeds ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4254]
  exact B4254.sound accepted4254
#print axioms checked4254

def Tip4249_4254 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4254 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4254
def B4313 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4313 : B4313.tree = HexagonCover.NBand.M8300_8500.SplitData.node4313 := by
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

def B4312 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4313, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4312 : B4312.tree = HexagonCover.NBand.M8300_8500.SplitData.node4312 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4313
  · rfl

def B4311 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B4312]
theorem treeEq4311 : B4311.tree = HexagonCover.NBand.M8300_8500.SplitData.node4311 := by
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
  · exact treeEq4312

def B4310 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B4311, (.leaf 0 [] 0)]
theorem treeEq4310 : B4310.tree = HexagonCover.NBand.M8300_8500.SplitData.node4310 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4311
  · rfl

def B4309 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B4310, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4309 : B4309.tree = HexagonCover.NBand.M8300_8500.SplitData.node4309 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4310
  · rfl

def B4253 : Block := .branch 98 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip4249_4254, B4309, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq4253 : B4253.tree = HexagonCover.NBand.M8300_8500.SplitData.node4253 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4309
  · rfl
  · rfl

def B4315 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4315 : B4315.tree = HexagonCover.NBand.M8300_8500.SplitData.node4315 := by
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
  · rfl

def B4314 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 24584, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4315, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq4314 : B4314.tree = HexagonCover.NBand.M8300_8500.SplitData.node4314 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4315
  · rfl
  · rfl
  · rfl

def B4252 : Block := .branch 90 ![2251799813685633, 504474076765488642, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B4253, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B4314]
theorem treeEq4252 : B4252.tree = HexagonCover.NBand.M8300_8500.SplitData.node4252 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4253
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4314

def B4317 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 77371252455336267181219848, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 687).pointIds 687), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4317 : B4317.tree = HexagonCover.NBand.M8300_8500.SplitData.node4317 := by
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
  · rfl

def B4316 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 77371252455336267181219848, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B4317]
theorem treeEq4316 : B4316.tree = HexagonCover.NBand.M8300_8500.SplitData.node4316 := by
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
  · exact treeEq4317

def B4251 : Block := .branch 86 ![2251799813685633, 504474076765488642, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4252, B4316, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4251 : B4251.tree = HexagonCover.NBand.M8300_8500.SplitData.node4251 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4252
  · exact treeEq4316
  · rfl
  · rfl
  · rfl

def B4319 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 158495010654756343320678522888, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 969).pointIds 969), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4319 : B4319.tree = HexagonCover.NBand.M8300_8500.SplitData.node4319 := by
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
  · rfl

def B4318 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 158495010654756343320678522888, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), (.leaf 3 (Common.fact 968).pointIds 968), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B4319]
theorem treeEq4318 : B4318.tree = HexagonCover.NBand.M8300_8500.SplitData.node4318 := by
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
  · exact treeEq4319

def B4250 : Block := .branch 85 ![2251799813685633, 504474076765488642, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4251, B4318, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4250 : B4250.tree = HexagonCover.NBand.M8300_8500.SplitData.node4250 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4251
  · exact treeEq4318
  · rfl
  · rfl
  · rfl

def B4321 : Block := .branch 161 ![385, 1538, 75557899754711342389252, 158475667841642509253883224072, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 971).pointIds 971), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4321 : B4321.tree = HexagonCover.NBand.M8300_8500.SplitData.node4321 := by
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
  · rfl

def B4320 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 158475667841642509253883224072, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B4321]
theorem treeEq4320 : B4320.tree = HexagonCover.NBand.M8300_8500.SplitData.node4320 := by
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
  · exact treeEq4321

def B4249 : Block := .branch 84 ![2251799813685633, 504474076765488642, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4250, B4320, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4249 : B4249.tree = HexagonCover.NBand.M8300_8500.SplitData.node4249 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4250
  · exact treeEq4320
  · rfl
  · rfl
  · rfl

theorem accepted4249 : B4249.accepted = true := by decide +kernel
theorem checked4249 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4249 (maskNeeds ![2251799813685633, 504474076765488642, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4249]
  exact B4249.sound accepted4249
#print axioms checked4249

def B4342 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 905).pointIds 905)]
theorem treeEq4342 : B4342.tree = HexagonCover.NBand.M8300_8500.SplitData.node4342 := by
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
  · rfl

def B4341 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4342, (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq4341 : B4341.tree = HexagonCover.NBand.M8300_8500.SplitData.node4341 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4342
  · rfl

def B4340 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4341, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4340 : B4340.tree = HexagonCover.NBand.M8300_8500.SplitData.node4340 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4341
  · rfl
  · rfl
  · rfl
  · rfl

def B4339 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4340, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4339 : B4339.tree = HexagonCover.NBand.M8300_8500.SplitData.node4339 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4340
  · rfl
  · rfl
  · rfl
  · rfl

def B4338 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4339, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4338 : B4338.tree = HexagonCover.NBand.M8300_8500.SplitData.node4338 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4339
  · rfl
  · rfl
  · rfl
  · rfl

def B4337 : Block := .branch 129 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B4338, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq4337 : B4337.tree = HexagonCover.NBand.M8300_8500.SplitData.node4337 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4338
  · rfl
  · rfl

def B4336 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B4337, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4336 : B4336.tree = HexagonCover.NBand.M8300_8500.SplitData.node4336 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4337
  · rfl
  · rfl

def B4335 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4336, (.leaf 0 [] 0)]
theorem treeEq4335 : B4335.tree = HexagonCover.NBand.M8300_8500.SplitData.node4335 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4336
  · rfl

def B4334 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4335, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4334 : B4334.tree = HexagonCover.NBand.M8300_8500.SplitData.node4334 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4335
  · rfl

def B4333 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B4334, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4333 : B4333.tree = HexagonCover.NBand.M8300_8500.SplitData.node4333 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4334
  · rfl
  · rfl

def B4332 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4333, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4332 : B4332.tree = HexagonCover.NBand.M8300_8500.SplitData.node4332 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4333
  · rfl
  · rfl
  · rfl

def B4331 : Block := .branch 161 ![2251799813685633, 360358888689632770, 113336831617668504098820, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 973).pointIds 973), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4332]
theorem treeEq4331 : B4331.tree = HexagonCover.NBand.M8300_8500.SplitData.node4331 := by
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
  · exact treeEq4332

theorem accepted4331 : B4331.accepted = true := by decide +kernel
theorem checked4331 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4331 (maskNeeds ![2251799813685633, 360358888689632770, 113336831617668504098820, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4331]
  exact B4331.sound accepted4331
#print axioms checked4331

def B4354 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq4354 : B4354.tree = HexagonCover.NBand.M8300_8500.SplitData.node4354 := by
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

def B4353 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4354, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq4353 : B4353.tree = HexagonCover.NBand.M8300_8500.SplitData.node4353 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4354
  · rfl

def B4352 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4353, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4352 : B4352.tree = HexagonCover.NBand.M8300_8500.SplitData.node4352 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4353
  · rfl
  · rfl
  · rfl
  · rfl

def B4351 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4352, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4351 : B4351.tree = HexagonCover.NBand.M8300_8500.SplitData.node4351 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4352
  · rfl
  · rfl
  · rfl
  · rfl

def B4350 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4351, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4350 : B4350.tree = HexagonCover.NBand.M8300_8500.SplitData.node4350 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4351
  · rfl
  · rfl
  · rfl
  · rfl

def B4349 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B4350, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4349 : B4349.tree = HexagonCover.NBand.M8300_8500.SplitData.node4349 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4350
  · rfl
  · rfl

def B4348 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4349, (.leaf 0 [] 0)]
theorem treeEq4348 : B4348.tree = HexagonCover.NBand.M8300_8500.SplitData.node4348 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4349
  · rfl

def B4347 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4348, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4347 : B4347.tree = HexagonCover.NBand.M8300_8500.SplitData.node4347 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4348
  · rfl

def B4346 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B4347, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4346 : B4346.tree = HexagonCover.NBand.M8300_8500.SplitData.node4346 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4347
  · rfl
  · rfl

def B4345 : Block := .branch 161 ![2251799813685633, 360358888689632770, 113336831617668504098820, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4346]
theorem treeEq4345 : B4345.tree = HexagonCover.NBand.M8300_8500.SplitData.node4345 := by
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
  · exact treeEq4346

def B4344 : Block := .branch 170 ![2251799813685633, 360358888689632770, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4345, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq4344 : B4344.tree = HexagonCover.NBand.M8300_8500.SplitData.node4344 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4345
  · rfl
  · rfl
  · rfl

def B4343 : Block := .branch 160 ![2251799813685633, 453384436202522049250818, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 689).pointIds 689), (.leaf 2 (Common.fact 1001).pointIds 1001), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B4344]
theorem treeEq4343 : B4343.tree = HexagonCover.NBand.M8300_8500.SplitData.node4343 := by
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
  · exact treeEq4344

theorem accepted4343 : B4343.accepted = true := by decide +kernel
theorem checked4343 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4343 (maskNeeds ![2251799813685633, 453384436202522049250818, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq4343]
  exact B4343.sound accepted4343
#print axioms checked4343

end HexagonCover.NBand.M8300_8500.SplitTree.Run0059
