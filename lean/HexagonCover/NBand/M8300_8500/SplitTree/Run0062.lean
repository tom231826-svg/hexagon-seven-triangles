import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0061
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0062
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip4489_4490 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4490 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0061.checked4490
def B4514 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4514 : B4514.tree = HexagonCover.NBand.M8300_8500.SplitData.node4514 := by
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

def B4513 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4514, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4513 : B4513.tree = HexagonCover.NBand.M8300_8500.SplitData.node4513 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4514
  · rfl
  · rfl
  · rfl

def B4512 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B4513]
theorem treeEq4512 : B4512.tree = HexagonCover.NBand.M8300_8500.SplitData.node4512 := by
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
  · exact treeEq4513

def B4518 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4518 : B4518.tree = HexagonCover.NBand.M8300_8500.SplitData.node4518 := by
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

def B4517 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4518, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4517 : B4517.tree = HexagonCover.NBand.M8300_8500.SplitData.node4517 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4518
  · rfl

def B4516 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4517]
theorem treeEq4516 : B4516.tree = HexagonCover.NBand.M8300_8500.SplitData.node4516 := by
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
  · exact treeEq4517

def B4515 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4516, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4515 : B4515.tree = HexagonCover.NBand.M8300_8500.SplitData.node4515 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4516
  · rfl
  · rfl
  · rfl

def B4511 : Block := .branch 125 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4512, B4515]
theorem treeEq4511 : B4511.tree = HexagonCover.NBand.M8300_8500.SplitData.node4511 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4512
  · exact treeEq4515

def B4522 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4522 : B4522.tree = HexagonCover.NBand.M8300_8500.SplitData.node4522 := by
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

def B4521 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4522, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4521 : B4521.tree = HexagonCover.NBand.M8300_8500.SplitData.node4521 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4522
  · rfl
  · rfl
  · rfl

def B4520 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B4521]
theorem treeEq4520 : B4520.tree = HexagonCover.NBand.M8300_8500.SplitData.node4520 := by
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
  · exact treeEq4521

def B4519 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4520, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4519 : B4519.tree = HexagonCover.NBand.M8300_8500.SplitData.node4519 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4520
  · rfl

def B4510 : Block := .branch 121 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B4511, (.leaf 5 (Common.fact 256).pointIds 256), B4519]
theorem treeEq4510 : B4510.tree = HexagonCover.NBand.M8300_8500.SplitData.node4510 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4511
  · rfl
  · exact treeEq4519

def B4527 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4527 : B4527.tree = HexagonCover.NBand.M8300_8500.SplitData.node4527 := by
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

def B4526 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4527, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4526 : B4526.tree = HexagonCover.NBand.M8300_8500.SplitData.node4526 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4527
  · rfl

def B4525 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4526]
theorem treeEq4525 : B4525.tree = HexagonCover.NBand.M8300_8500.SplitData.node4525 := by
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
  · exact treeEq4526

def B4524 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4525, (.leaf 0 [] 0)]
theorem treeEq4524 : B4524.tree = HexagonCover.NBand.M8300_8500.SplitData.node4524 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4525
  · rfl

def B4523 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4524, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4523 : B4523.tree = HexagonCover.NBand.M8300_8500.SplitData.node4523 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4524
  · rfl

def B4509 : Block := .branch 119 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4510, B4523, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4509 : B4509.tree = HexagonCover.NBand.M8300_8500.SplitData.node4509 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4510
  · exact treeEq4523
  · rfl
  · rfl

def B4489 : Block := .branch 115 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4489_4490, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B4509, (.leaf 0 [] 0)]
theorem treeEq4489 : B4489.tree = HexagonCover.NBand.M8300_8500.SplitData.node4489 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4509
  · rfl

theorem accepted4489 : B4489.accepted = true := by decide +kernel
theorem checked4489 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4489 (maskNeeds ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4489]
  exact B4489.sound accepted4489
#print axioms checked4489

def Tip4486_4489 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4489 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4489
def B4531 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq4531 : B4531.tree = HexagonCover.NBand.M8300_8500.SplitData.node4531 := by
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

def B4530 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4531, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq4530 : B4530.tree = HexagonCover.NBand.M8300_8500.SplitData.node4530 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4531
  · rfl
  · rfl
  · rfl

def B4529 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400333925883571647971334348810992746560] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4530]
theorem treeEq4529 : B4529.tree = HexagonCover.NBand.M8300_8500.SplitData.node4529 := by
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
  · exact treeEq4530

def B4528 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772933191195142415830470672991745736768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4529, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq4528 : B4528.tree = HexagonCover.NBand.M8300_8500.SplitData.node4528 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4529
  · rfl

def B4488 : Block := .branch 113 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4486_4489, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B4528]
theorem treeEq4488 : B4488.tree = HexagonCover.NBand.M8300_8500.SplitData.node4488 := by
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
  · exact treeEq4528

def B4536 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4536 : B4536.tree = HexagonCover.NBand.M8300_8500.SplitData.node4536 := by
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

def B4535 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4536, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4535 : B4535.tree = HexagonCover.NBand.M8300_8500.SplitData.node4535 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4536
  · rfl

def B4534 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B4535]
theorem treeEq4534 : B4534.tree = HexagonCover.NBand.M8300_8500.SplitData.node4534 := by
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
  · exact treeEq4535

def B4533 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B4534, (.leaf 0 [] 0)]
theorem treeEq4533 : B4533.tree = HexagonCover.NBand.M8300_8500.SplitData.node4533 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4534
  · rfl

def B4532 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B4533, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4532 : B4532.tree = HexagonCover.NBand.M8300_8500.SplitData.node4532 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4533
  · rfl

def B4487 : Block := .branch 108 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B4488, B4532, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq4487 : B4487.tree = HexagonCover.NBand.M8300_8500.SplitData.node4487 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4488
  · exact treeEq4532
  · rfl
  · rfl

def B4540 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq4540 : B4540.tree = HexagonCover.NBand.M8300_8500.SplitData.node4540 := by
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

def B4539 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4540, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq4539 : B4539.tree = HexagonCover.NBand.M8300_8500.SplitData.node4539 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4540
  · rfl
  · rfl
  · rfl

def B4538 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400323542557505178544306689315037511744] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4539]
theorem treeEq4538 : B4538.tree = HexagonCover.NBand.M8300_8500.SplitData.node4538 := by
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
  · exact treeEq4539

def B4537 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922807869075946403443013495790501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4538, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4537 : B4537.tree = HexagonCover.NBand.M8300_8500.SplitData.node4537 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4538
  · rfl

def B4486 : Block := .branch 100 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B4487, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B4537]
theorem treeEq4486 : B4486.tree = HexagonCover.NBand.M8300_8500.SplitData.node4486 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4487
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4537

theorem accepted4486 : B4486.accepted = true := by decide +kernel
theorem checked4486 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4486 (maskNeeds ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4486]
  exact B4486.sound accepted4486
#print axioms checked4486

def Tip4481_4486 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4486 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4486
def B4545 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4545 : B4545.tree = HexagonCover.NBand.M8300_8500.SplitData.node4545 := by
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

def B4544 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4545, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4544 : B4544.tree = HexagonCover.NBand.M8300_8500.SplitData.node4544 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4545
  · rfl

def B4543 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B4544]
theorem treeEq4543 : B4543.tree = HexagonCover.NBand.M8300_8500.SplitData.node4543 := by
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
  · exact treeEq4544

def B4542 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B4543, (.leaf 0 [] 0)]
theorem treeEq4542 : B4542.tree = HexagonCover.NBand.M8300_8500.SplitData.node4542 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4543
  · rfl

def B4541 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B4542, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4541 : B4541.tree = HexagonCover.NBand.M8300_8500.SplitData.node4541 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4542
  · rfl

def B4485 : Block := .branch 98 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip4481_4486, B4541, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq4485 : B4485.tree = HexagonCover.NBand.M8300_8500.SplitData.node4485 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4541
  · rfl
  · rfl

def B4547 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4547 : B4547.tree = HexagonCover.NBand.M8300_8500.SplitData.node4547 := by
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

def B4546 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 24584, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4547, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq4546 : B4546.tree = HexagonCover.NBand.M8300_8500.SplitData.node4546 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4547
  · rfl
  · rfl
  · rfl

def B4484 : Block := .branch 90 ![2251799813685633, 504474076765488642, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B4485, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B4546]
theorem treeEq4484 : B4484.tree = HexagonCover.NBand.M8300_8500.SplitData.node4484 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4485
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4546

def B4549 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 77371252455336267181219848, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 687).pointIds 687), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4549 : B4549.tree = HexagonCover.NBand.M8300_8500.SplitData.node4549 := by
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

def B4548 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 77371252455336267181219848, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B4549]
theorem treeEq4548 : B4548.tree = HexagonCover.NBand.M8300_8500.SplitData.node4548 := by
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
  · exact treeEq4549

def B4483 : Block := .branch 86 ![2251799813685633, 504474076765488642, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4484, B4548, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4483 : B4483.tree = HexagonCover.NBand.M8300_8500.SplitData.node4483 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4484
  · exact treeEq4548
  · rfl
  · rfl
  · rfl

def B4551 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 158495010654756343320678522888, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 969).pointIds 969), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4551 : B4551.tree = HexagonCover.NBand.M8300_8500.SplitData.node4551 := by
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

def B4550 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 158495010654756343320678522888, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), (.leaf 3 (Common.fact 968).pointIds 968), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B4551]
theorem treeEq4550 : B4550.tree = HexagonCover.NBand.M8300_8500.SplitData.node4550 := by
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
  · exact treeEq4551

def B4482 : Block := .branch 85 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4483, B4550, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4482 : B4482.tree = HexagonCover.NBand.M8300_8500.SplitData.node4482 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4483
  · exact treeEq4550
  · rfl
  · rfl
  · rfl

def B4553 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 158475667841642509253883224072, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 971).pointIds 971), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4553 : B4553.tree = HexagonCover.NBand.M8300_8500.SplitData.node4553 := by
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

def B4552 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 158475667841642509253883224072, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B4553]
theorem treeEq4552 : B4552.tree = HexagonCover.NBand.M8300_8500.SplitData.node4552 := by
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
  · exact treeEq4553

def B4481 : Block := .branch 84 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4482, B4552, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4481 : B4481.tree = HexagonCover.NBand.M8300_8500.SplitData.node4481 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4482
  · exact treeEq4552
  · rfl
  · rfl
  · rfl

theorem accepted4481 : B4481.accepted = true := by decide +kernel
theorem checked4481 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4481 (maskNeeds ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4481]
  exact B4481.sound accepted4481
#print axioms checked4481

def B4574 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 905).pointIds 905)]
theorem treeEq4574 : B4574.tree = HexagonCover.NBand.M8300_8500.SplitData.node4574 := by
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

def B4573 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4574, (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq4573 : B4573.tree = HexagonCover.NBand.M8300_8500.SplitData.node4573 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4574
  · rfl

def B4572 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4573, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4572 : B4572.tree = HexagonCover.NBand.M8300_8500.SplitData.node4572 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4573
  · rfl
  · rfl
  · rfl
  · rfl

def B4571 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4572, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4571 : B4571.tree = HexagonCover.NBand.M8300_8500.SplitData.node4571 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4572
  · rfl
  · rfl
  · rfl
  · rfl

def B4570 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4571, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4570 : B4570.tree = HexagonCover.NBand.M8300_8500.SplitData.node4570 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4571
  · rfl
  · rfl
  · rfl
  · rfl

def B4569 : Block := .branch 129 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B4570, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq4569 : B4569.tree = HexagonCover.NBand.M8300_8500.SplitData.node4569 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4570
  · rfl
  · rfl

def B4568 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B4569, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4568 : B4568.tree = HexagonCover.NBand.M8300_8500.SplitData.node4568 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4569
  · rfl
  · rfl

def B4567 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4568, (.leaf 0 [] 0)]
theorem treeEq4567 : B4567.tree = HexagonCover.NBand.M8300_8500.SplitData.node4567 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4568
  · rfl

def B4566 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4567, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4566 : B4566.tree = HexagonCover.NBand.M8300_8500.SplitData.node4566 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4567
  · rfl

def B4565 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B4566, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4565 : B4565.tree = HexagonCover.NBand.M8300_8500.SplitData.node4565 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4566
  · rfl
  · rfl

def B4564 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4565, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4564 : B4564.tree = HexagonCover.NBand.M8300_8500.SplitData.node4564 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4565
  · rfl
  · rfl
  · rfl

def B4563 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 973).pointIds 973), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4564]
theorem treeEq4563 : B4563.tree = HexagonCover.NBand.M8300_8500.SplitData.node4563 := by
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
  · exact treeEq4564

theorem accepted4563 : B4563.accepted = true := by decide +kernel
theorem checked4563 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4563 (maskNeeds ![2251799813685633, 360358888689632770, 37815861379901599782916, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4563]
  exact B4563.sound accepted4563
#print axioms checked4563

def B4586 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq4586 : B4586.tree = HexagonCover.NBand.M8300_8500.SplitData.node4586 := by
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

def B4585 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4586, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq4585 : B4585.tree = HexagonCover.NBand.M8300_8500.SplitData.node4585 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4586
  · rfl

def B4584 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4585, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4584 : B4584.tree = HexagonCover.NBand.M8300_8500.SplitData.node4584 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4585
  · rfl
  · rfl
  · rfl
  · rfl

def B4583 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4584, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4583 : B4583.tree = HexagonCover.NBand.M8300_8500.SplitData.node4583 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4584
  · rfl
  · rfl
  · rfl
  · rfl

def B4582 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4583, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4582 : B4582.tree = HexagonCover.NBand.M8300_8500.SplitData.node4582 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4583
  · rfl
  · rfl
  · rfl
  · rfl

def B4581 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B4582, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4581 : B4581.tree = HexagonCover.NBand.M8300_8500.SplitData.node4581 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4582
  · rfl
  · rfl

def B4580 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4581, (.leaf 0 [] 0)]
theorem treeEq4580 : B4580.tree = HexagonCover.NBand.M8300_8500.SplitData.node4580 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4581
  · rfl

def B4579 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4580, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4579 : B4579.tree = HexagonCover.NBand.M8300_8500.SplitData.node4579 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4580
  · rfl

def B4578 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B4579, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4578 : B4578.tree = HexagonCover.NBand.M8300_8500.SplitData.node4578 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4579
  · rfl
  · rfl

def B4577 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4578]
theorem treeEq4577 : B4577.tree = HexagonCover.NBand.M8300_8500.SplitData.node4577 := by
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
  · exact treeEq4578

def B4576 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4577, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq4576 : B4576.tree = HexagonCover.NBand.M8300_8500.SplitData.node4576 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4577
  · rfl
  · rfl
  · rfl

def B4575 : Block := .branch 160 ![2251799813685633, 453347542714374630147586, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1005).pointIds 1005), (.leaf 2 (Common.fact 1001).pointIds 1001), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B4576]
theorem treeEq4575 : B4575.tree = HexagonCover.NBand.M8300_8500.SplitData.node4575 := by
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
  · exact treeEq4576

theorem accepted4575 : B4575.accepted = true := by decide +kernel
theorem checked4575 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4575 (maskNeeds ![2251799813685633, 453347542714374630147586, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq4575]
  exact B4575.sound accepted4575
#print axioms checked4575

end HexagonCover.NBand.M8300_8500.SplitTree.Run0062
