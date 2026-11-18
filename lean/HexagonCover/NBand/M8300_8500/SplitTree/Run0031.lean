import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0030
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0031
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip2261_2262 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2262 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0030.checked2262
def B2286 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq2286 : B2286.tree = HexagonCover.NBand.M8300_8500.SplitData.node2286 := by
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

def B2285 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2286, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq2285 : B2285.tree = HexagonCover.NBand.M8300_8500.SplitData.node2285 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2286
  · rfl
  · rfl
  · rfl

def B2284 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B2285]
theorem treeEq2284 : B2284.tree = HexagonCover.NBand.M8300_8500.SplitData.node2284 := by
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
  · exact treeEq2285

def B2290 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq2290 : B2290.tree = HexagonCover.NBand.M8300_8500.SplitData.node2290 := by
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

def B2289 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2290, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq2289 : B2289.tree = HexagonCover.NBand.M8300_8500.SplitData.node2289 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2290
  · rfl

def B2288 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2289]
theorem treeEq2288 : B2288.tree = HexagonCover.NBand.M8300_8500.SplitData.node2288 := by
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
  · exact treeEq2289

def B2287 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2288, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2287 : B2287.tree = HexagonCover.NBand.M8300_8500.SplitData.node2287 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2288
  · rfl
  · rfl
  · rfl

def B2283 : Block := .branch 125 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B2284, B2287]
theorem treeEq2283 : B2283.tree = HexagonCover.NBand.M8300_8500.SplitData.node2283 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2284
  · exact treeEq2287

def B2294 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2294 : B2294.tree = HexagonCover.NBand.M8300_8500.SplitData.node2294 := by
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

def B2293 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2294, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2293 : B2293.tree = HexagonCover.NBand.M8300_8500.SplitData.node2293 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2294
  · rfl
  · rfl
  · rfl

def B2292 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B2293]
theorem treeEq2292 : B2292.tree = HexagonCover.NBand.M8300_8500.SplitData.node2292 := by
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
  · exact treeEq2293

def B2291 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2292, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq2291 : B2291.tree = HexagonCover.NBand.M8300_8500.SplitData.node2291 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2292
  · rfl

def B2282 : Block := .branch 121 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B2283, (.leaf 5 (Common.fact 256).pointIds 256), B2291]
theorem treeEq2282 : B2282.tree = HexagonCover.NBand.M8300_8500.SplitData.node2282 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2283
  · rfl
  · exact treeEq2291

def B2299 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2299 : B2299.tree = HexagonCover.NBand.M8300_8500.SplitData.node2299 := by
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

def B2298 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2299, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2298 : B2298.tree = HexagonCover.NBand.M8300_8500.SplitData.node2298 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2299
  · rfl

def B2297 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B2298]
theorem treeEq2297 : B2297.tree = HexagonCover.NBand.M8300_8500.SplitData.node2297 := by
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
  · exact treeEq2298

def B2296 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B2297, (.leaf 0 [] 0)]
theorem treeEq2296 : B2296.tree = HexagonCover.NBand.M8300_8500.SplitData.node2296 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2297
  · rfl

def B2295 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B2296, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2295 : B2295.tree = HexagonCover.NBand.M8300_8500.SplitData.node2295 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2296
  · rfl

def B2281 : Block := .branch 119 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B2282, B2295, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2281 : B2281.tree = HexagonCover.NBand.M8300_8500.SplitData.node2281 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2282
  · exact treeEq2295
  · rfl
  · rfl

def B2261 : Block := .branch 115 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip2261_2262, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B2281, (.leaf 0 [] 0)]
theorem treeEq2261 : B2261.tree = HexagonCover.NBand.M8300_8500.SplitData.node2261 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2281
  · rfl

theorem accepted2261 : B2261.accepted = true := by decide +kernel
theorem checked2261 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2261 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2261]
  exact B2261.sound accepted2261
#print axioms checked2261

def Tip2258_2261 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2261 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked2261
def B2303 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq2303 : B2303.tree = HexagonCover.NBand.M8300_8500.SplitData.node2303 := by
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

def B2302 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2303, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2302 : B2302.tree = HexagonCover.NBand.M8300_8500.SplitData.node2302 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2303
  · rfl
  · rfl
  · rfl

def B2301 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400333925883571647971334348810992746560] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B2302]
theorem treeEq2301 : B2301.tree = HexagonCover.NBand.M8300_8500.SplitData.node2301 := by
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
  · exact treeEq2302

def B2300 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772933191195142415830470672991745736768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2301, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq2300 : B2300.tree = HexagonCover.NBand.M8300_8500.SplitData.node2300 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2301
  · rfl

def B2260 : Block := .branch 113 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip2258_2261, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B2300]
theorem treeEq2260 : B2260.tree = HexagonCover.NBand.M8300_8500.SplitData.node2260 := by
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
  · exact treeEq2300

def B2308 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2308 : B2308.tree = HexagonCover.NBand.M8300_8500.SplitData.node2308 := by
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

def B2307 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2308, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2307 : B2307.tree = HexagonCover.NBand.M8300_8500.SplitData.node2307 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2308
  · rfl

def B2306 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B2307]
theorem treeEq2306 : B2306.tree = HexagonCover.NBand.M8300_8500.SplitData.node2306 := by
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
  · exact treeEq2307

def B2305 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B2306, (.leaf 0 [] 0)]
theorem treeEq2305 : B2305.tree = HexagonCover.NBand.M8300_8500.SplitData.node2305 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2306
  · rfl

def B2304 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B2305, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2304 : B2304.tree = HexagonCover.NBand.M8300_8500.SplitData.node2304 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2305
  · rfl

def B2259 : Block := .branch 108 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B2260, B2304, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq2259 : B2259.tree = HexagonCover.NBand.M8300_8500.SplitData.node2259 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2260
  · exact treeEq2304
  · rfl
  · rfl

def B2312 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2312 : B2312.tree = HexagonCover.NBand.M8300_8500.SplitData.node2312 := by
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

def B2311 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2312, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq2311 : B2311.tree = HexagonCover.NBand.M8300_8500.SplitData.node2311 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2312
  · rfl
  · rfl
  · rfl

def B2310 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400323542557505178544306689315037511744] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B2311]
theorem treeEq2310 : B2310.tree = HexagonCover.NBand.M8300_8500.SplitData.node2310 := by
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
  · exact treeEq2311

def B2309 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922807869075946403443013495790501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2310, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2309 : B2309.tree = HexagonCover.NBand.M8300_8500.SplitData.node2309 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2310
  · rfl

def B2258 : Block := .branch 100 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B2259, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B2309]
theorem treeEq2258 : B2258.tree = HexagonCover.NBand.M8300_8500.SplitData.node2258 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2259
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2309

theorem accepted2258 : B2258.accepted = true := by decide +kernel
theorem checked2258 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2258 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2258]
  exact B2258.sound accepted2258
#print axioms checked2258

def Tip2253_2258 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2258 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked2258
def B2317 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2317 : B2317.tree = HexagonCover.NBand.M8300_8500.SplitData.node2317 := by
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

def B2316 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2317, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2316 : B2316.tree = HexagonCover.NBand.M8300_8500.SplitData.node2316 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2317
  · rfl

def B2315 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B2316]
theorem treeEq2315 : B2315.tree = HexagonCover.NBand.M8300_8500.SplitData.node2315 := by
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
  · exact treeEq2316

def B2314 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B2315, (.leaf 0 [] 0)]
theorem treeEq2314 : B2314.tree = HexagonCover.NBand.M8300_8500.SplitData.node2314 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2315
  · rfl

def B2313 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B2314, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2313 : B2313.tree = HexagonCover.NBand.M8300_8500.SplitData.node2313 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2314
  · rfl

def B2257 : Block := .branch 98 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip2253_2258, B2313, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq2257 : B2257.tree = HexagonCover.NBand.M8300_8500.SplitData.node2257 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2313
  · rfl
  · rfl

def B2319 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq2319 : B2319.tree = HexagonCover.NBand.M8300_8500.SplitData.node2319 := by
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

def B2318 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 24584, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2319, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq2318 : B2318.tree = HexagonCover.NBand.M8300_8500.SplitData.node2318 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2319
  · rfl
  · rfl
  · rfl

def B2256 : Block := .branch 90 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B2257, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B2318]
theorem treeEq2256 : B2256.tree = HexagonCover.NBand.M8300_8500.SplitData.node2256 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2257
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2318

def B2321 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 77371252455336267181219848, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 687).pointIds 687), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2321 : B2321.tree = HexagonCover.NBand.M8300_8500.SplitData.node2321 := by
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

def B2320 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 77371252455336267181219848, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2321]
theorem treeEq2320 : B2320.tree = HexagonCover.NBand.M8300_8500.SplitData.node2320 := by
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
  · exact treeEq2321

def B2255 : Block := .branch 86 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2256, B2320, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2255 : B2255.tree = HexagonCover.NBand.M8300_8500.SplitData.node2255 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2256
  · exact treeEq2320
  · rfl
  · rfl
  · rfl

def B2323 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 158495010654756343320678522888, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 969).pointIds 969), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2323 : B2323.tree = HexagonCover.NBand.M8300_8500.SplitData.node2323 := by
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

def B2322 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 158495010654756343320678522888, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), (.leaf 3 (Common.fact 968).pointIds 968), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2323]
theorem treeEq2322 : B2322.tree = HexagonCover.NBand.M8300_8500.SplitData.node2322 := by
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
  · exact treeEq2323

def B2254 : Block := .branch 85 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2255, B2322, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2254 : B2254.tree = HexagonCover.NBand.M8300_8500.SplitData.node2254 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2255
  · exact treeEq2322
  · rfl
  · rfl
  · rfl

def B2325 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 158475667841642509253883224072, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 971).pointIds 971), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2325 : B2325.tree = HexagonCover.NBand.M8300_8500.SplitData.node2325 := by
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

def B2324 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 158475667841642509253883224072, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2325]
theorem treeEq2324 : B2324.tree = HexagonCover.NBand.M8300_8500.SplitData.node2324 := by
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
  · exact treeEq2325

def B2253 : Block := .branch 84 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2254, B2324, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2253 : B2253.tree = HexagonCover.NBand.M8300_8500.SplitData.node2253 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2254
  · exact treeEq2324
  · rfl
  · rfl
  · rfl

theorem accepted2253 : B2253.accepted = true := by decide +kernel
theorem checked2253 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2253 (maskNeeds ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2253]
  exact B2253.sound accepted2253
#print axioms checked2253

def B2346 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 905).pointIds 905)]
theorem treeEq2346 : B2346.tree = HexagonCover.NBand.M8300_8500.SplitData.node2346 := by
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

def B2345 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2346, (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2345 : B2345.tree = HexagonCover.NBand.M8300_8500.SplitData.node2345 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2346
  · rfl

def B2344 : Block := .branch 84 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2345, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2344 : B2344.tree = HexagonCover.NBand.M8300_8500.SplitData.node2344 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2345
  · rfl
  · rfl
  · rfl
  · rfl

def B2343 : Block := .branch 85 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2344, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2343 : B2343.tree = HexagonCover.NBand.M8300_8500.SplitData.node2343 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2344
  · rfl
  · rfl
  · rfl
  · rfl

def B2342 : Block := .branch 86 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2343, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2342 : B2342.tree = HexagonCover.NBand.M8300_8500.SplitData.node2342 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2343
  · rfl
  · rfl
  · rfl
  · rfl

def B2341 : Block := .branch 129 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B2342, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2341 : B2341.tree = HexagonCover.NBand.M8300_8500.SplitData.node2341 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2342
  · rfl
  · rfl

def B2340 : Block := .branch 138 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B2341, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2340 : B2340.tree = HexagonCover.NBand.M8300_8500.SplitData.node2340 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2341
  · rfl
  · rfl

def B2339 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2340, (.leaf 0 [] 0)]
theorem treeEq2339 : B2339.tree = HexagonCover.NBand.M8300_8500.SplitData.node2339 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2340
  · rfl

def B2338 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2339, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2338 : B2338.tree = HexagonCover.NBand.M8300_8500.SplitData.node2338 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2339
  · rfl

def B2337 : Block := .branch 146 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B2338, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2337 : B2337.tree = HexagonCover.NBand.M8300_8500.SplitData.node2337 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2338
  · rfl
  · rfl

def B2336 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2337, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2336 : B2336.tree = HexagonCover.NBand.M8300_8500.SplitData.node2336 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2337
  · rfl
  · rfl
  · rfl

def B2335 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 973).pointIds 973), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2336]
theorem treeEq2335 : B2335.tree = HexagonCover.NBand.M8300_8500.SplitData.node2335 := by
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
  · exact treeEq2336

theorem accepted2335 : B2335.accepted = true := by decide +kernel
theorem checked2335 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2335 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq2335]
  exact B2335.sound accepted2335
#print axioms checked2335

def B2358 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq2358 : B2358.tree = HexagonCover.NBand.M8300_8500.SplitData.node2358 := by
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

def B2357 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2358, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq2357 : B2357.tree = HexagonCover.NBand.M8300_8500.SplitData.node2357 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2358
  · rfl

def B2356 : Block := .branch 84 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2357, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2356 : B2356.tree = HexagonCover.NBand.M8300_8500.SplitData.node2356 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2357
  · rfl
  · rfl
  · rfl
  · rfl

def B2355 : Block := .branch 85 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2356, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2355 : B2355.tree = HexagonCover.NBand.M8300_8500.SplitData.node2355 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2356
  · rfl
  · rfl
  · rfl
  · rfl

def B2354 : Block := .branch 86 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2355, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2354 : B2354.tree = HexagonCover.NBand.M8300_8500.SplitData.node2354 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2355
  · rfl
  · rfl
  · rfl
  · rfl

def B2353 : Block := .branch 138 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B2354, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2353 : B2353.tree = HexagonCover.NBand.M8300_8500.SplitData.node2353 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2354
  · rfl
  · rfl

def B2352 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2353, (.leaf 0 [] 0)]
theorem treeEq2352 : B2352.tree = HexagonCover.NBand.M8300_8500.SplitData.node2352 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2353
  · rfl

def B2351 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2352, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2351 : B2351.tree = HexagonCover.NBand.M8300_8500.SplitData.node2351 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2352
  · rfl

def B2350 : Block := .branch 146 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B2351, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2350 : B2350.tree = HexagonCover.NBand.M8300_8500.SplitData.node2350 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2351
  · rfl
  · rfl

def B2349 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2350]
theorem treeEq2349 : B2349.tree = HexagonCover.NBand.M8300_8500.SplitData.node2349 := by
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
  · exact treeEq2350

def B2348 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2349, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq2348 : B2348.tree = HexagonCover.NBand.M8300_8500.SplitData.node2348 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2349
  · rfl
  · rfl
  · rfl

def B2347 : Block := .branch 160 ![578712552117109121, 453347578672802904933890, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 977).pointIds 977), (.leaf 2 (Common.fact 975).pointIds 975), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B2348]
theorem treeEq2347 : B2347.tree = HexagonCover.NBand.M8300_8500.SplitData.node2347 := by
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
  · exact treeEq2348

theorem accepted2347 : B2347.accepted = true := by decide +kernel
theorem checked2347 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2347 (maskNeeds ![578712552117109121, 453347578672802904933890, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq2347]
  exact B2347.sound accepted2347
#print axioms checked2347

end HexagonCover.NBand.M8300_8500.SplitTree.Run0031
