import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0046
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0047
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3427_3428 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3428 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] HexagonCover.NBand.M6667_6700.SplitTree.Run0046.checked3428
def B3449 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3449 : B3449.tree = HexagonCover.NBand.M6667_6700.SplitData.node3449 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3448 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3449]
theorem treeEq3448 : B3448.tree = HexagonCover.NBand.M6667_6700.SplitData.node3448 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3449

def B3451 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq3451 : B3451.tree = HexagonCover.NBand.M6667_6700.SplitData.node3451 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3450 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3451, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3450 : B3450.tree = HexagonCover.NBand.M6667_6700.SplitData.node3450 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3451
  · rfl
  · rfl

def B3447 : Block := .branch 128 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B3448, (.leaf 5 (Common.fact 439).pointIds 439), B3450]
theorem treeEq3447 : B3447.tree = HexagonCover.NBand.M6667_6700.SplitData.node3447 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3448
  · rfl
  · exact treeEq3450

def B3453 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3453 : B3453.tree = HexagonCover.NBand.M6667_6700.SplitData.node3453 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3452 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3453]
theorem treeEq3452 : B3452.tree = HexagonCover.NBand.M6667_6700.SplitData.node3452 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3453

def B3446 : Block := .branch 127 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376686569847858686053580864] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3447, B3452, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3446 : B3446.tree = HexagonCover.NBand.M6667_6700.SplitData.node3446 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3447
  · exact treeEq3452
  · rfl
  · rfl

def B3456 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894347817055727507503317056] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3456 : B3456.tree = HexagonCover.NBand.M6667_6700.SplitData.node3456 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3455 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053356944869431472157655302208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3456]
theorem treeEq3455 : B3455.tree = HexagonCover.NBand.M6667_6700.SplitData.node3455 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3456

def B3454 : Block := .branch 167 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818557646125237003065387937758183488] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3455, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3454 : B3454.tree = HexagonCover.NBand.M6667_6700.SplitData.node3454 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3455
  · rfl
  · rfl

def B3445 : Block := .branch 125 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3446, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3454, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3445 : B3445.tree = HexagonCover.NBand.M6667_6700.SplitData.node3445 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3446
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3454
  · rfl

def B3459 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3459 : B3459.tree = HexagonCover.NBand.M6667_6700.SplitData.node3459 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3458 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3459]
theorem treeEq3458 : B3458.tree = HexagonCover.NBand.M6667_6700.SplitData.node3458 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3459

def B3457 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3458, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3457 : B3457.tree = HexagonCover.NBand.M6667_6700.SplitData.node3457 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3458
  · rfl
  · rfl

def B3444 : Block := .branch 123 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3445, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3457]
theorem treeEq3444 : B3444.tree = HexagonCover.NBand.M6667_6700.SplitData.node3444 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3445
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3457

def B3427 : Block := .branch 74 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip3427_3428, B3444, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 1027).pointIds 1027)]
theorem treeEq3427 : B3427.tree = HexagonCover.NBand.M6667_6700.SplitData.node3427 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3444
  · rfl
  · rfl
  · rfl

theorem accepted3427 : B3427.accepted = true := by decide +kernel
theorem checked3427 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3427 (maskNeeds ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272]) := by
  rw [← treeEq3427]
  exact B3427.sound accepted3427
#print axioms checked3427

def Tip3374_3385 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3385 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] HexagonCover.NBand.M6667_6700.SplitTree.Run0046.checked3385
def Tip3374_3427 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3427 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272] checked3427
def B3380 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525890138169906551896670272] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1290).pointIds 1290)]
theorem treeEq3380 : B3380.tree = HexagonCover.NBand.M6667_6700.SplitData.node3380 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3379 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525890138169906551896670272] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3380, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1289).pointIds 1289)]
theorem treeEq3379 : B3379.tree = HexagonCover.NBand.M6667_6700.SplitData.node3379 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3380
  · rfl
  · rfl

def B3378 : Block := .branch 160 ![385, 1538, 80280230209883480266756, 29016580853992535015579656, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841057421886886895964127296] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1287).pointIds 1287), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3379]
theorem treeEq3378 : B3378.tree = HexagonCover.NBand.M6667_6700.SplitData.node3378 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3379

def B3384 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525890138169906551896670272] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1290).pointIds 1290)]
theorem treeEq3384 : B3384.tree = HexagonCover.NBand.M6667_6700.SplitData.node3384 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3383 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525890138169906551896670272] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3384, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1289).pointIds 1289)]
theorem treeEq3383 : B3383.tree = HexagonCover.NBand.M6667_6700.SplitData.node3383 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3384
  · rfl
  · rfl

def B3382 : Block := .branch 160 ![385, 1538, 85002596692753125480452, 29016580853992535015579656, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841057421886886895964127296] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1291).pointIds 1291), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3383]
theorem treeEq3382 : B3382.tree = HexagonCover.NBand.M6667_6700.SplitData.node3382 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3383

def B3381 : Block := .branch 73 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), B3382, Tip3374_3385, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 1023).pointIds 1023)]
theorem treeEq3381 : B3381.tree = HexagonCover.NBand.M6667_6700.SplitData.node3381 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3382
  · rfl
  · rfl
  · rfl
  · rfl

def B3377 : Block := .branch 72 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3378, B3381, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1015).pointIds 1015)]
theorem treeEq3377 : B3377.tree = HexagonCover.NBand.M6667_6700.SplitData.node3377 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3378
  · exact treeEq3381
  · rfl
  · rfl
  · rfl

def B3376 : Block := .branch 140 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3377, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq3376 : B3376.tree = HexagonCover.NBand.M6667_6700.SplitData.node3376 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3377
  · rfl
  · rfl

def B3375 : Block := .branch 163 ![5319508131568930906582414993892835713, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B3376]
theorem treeEq3375 : B3375.tree = HexagonCover.NBand.M6667_6700.SplitData.node3375 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3376

def B3422 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186891899520977545557704768] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1293).pointIds 1293)]
theorem treeEq3422 : B3422.tree = HexagonCover.NBand.M6667_6700.SplitData.node3422 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3421 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186891899520977545557704768] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3422, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1292).pointIds 1292)]
theorem treeEq3421 : B3421.tree = HexagonCover.NBand.M6667_6700.SplitData.node3421 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3422
  · rfl
  · rfl

def B3420 : Block := .branch 160 ![385, 1538, 80280230209883480266756, 29016580853992535015579656, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502059183237957889625161792] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1287).pointIds 1287), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3421]
theorem treeEq3420 : B3420.tree = HexagonCover.NBand.M6667_6700.SplitData.node3420 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3421

def B3426 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186891899520977545557704768] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1293).pointIds 1293)]
theorem treeEq3426 : B3426.tree = HexagonCover.NBand.M6667_6700.SplitData.node3426 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3425 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186891899520977545557704768] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3426, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1292).pointIds 1292)]
theorem treeEq3425 : B3425.tree = HexagonCover.NBand.M6667_6700.SplitData.node3425 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3426
  · rfl
  · rfl

def B3424 : Block := .branch 160 ![385, 1538, 85002596692753125480452, 29016580853992535015579656, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502059183237957889625161792] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1291).pointIds 1291), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3425]
theorem treeEq3424 : B3424.tree = HexagonCover.NBand.M6667_6700.SplitData.node3424 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3425

def B3423 : Block := .branch 73 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), B3424, Tip3374_3427, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 1026).pointIds 1026)]
theorem treeEq3423 : B3423.tree = HexagonCover.NBand.M6667_6700.SplitData.node3423 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3424
  · rfl
  · rfl
  · rfl
  · rfl

def B3419 : Block := .branch 72 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3420, B3423, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq3419 : B3419.tree = HexagonCover.NBand.M6667_6700.SplitData.node3419 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3420
  · exact treeEq3423
  · rfl
  · rfl
  · rfl

def B3418 : Block := .branch 140 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3419, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq3418 : B3418.tree = HexagonCover.NBand.M6667_6700.SplitData.node3418 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3419
  · rfl
  · rfl

def B3374 : Block := .branch 122 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![B3375, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B3418]
theorem treeEq3374 : B3374.tree = HexagonCover.NBand.M6667_6700.SplitData.node3374 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3375
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3418

theorem accepted3374 : B3374.accepted = true := by decide +kernel
theorem checked3374 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3374 (maskNeeds ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq3374]
  exact B3374.sound accepted3374
#print axioms checked3374

def Tip3364_3374 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3374 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] checked3374
def B3366 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq3366 : B3366.tree = HexagonCover.NBand.M6667_6700.SplitData.node3366 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3365 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3366]
theorem treeEq3365 : B3365.tree = HexagonCover.NBand.M6667_6700.SplitData.node3365 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3366

def B3370 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq3370 : B3370.tree = HexagonCover.NBand.M6667_6700.SplitData.node3370 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3369 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B3370]
theorem treeEq3369 : B3369.tree = HexagonCover.NBand.M6667_6700.SplitData.node3369 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3370

def B3373 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq3373 : B3373.tree = HexagonCover.NBand.M6667_6700.SplitData.node3373 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3372 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B3373]
theorem treeEq3372 : B3372.tree = HexagonCover.NBand.M6667_6700.SplitData.node3372 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3373

def B3371 : Block := .branch 121 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664091495487973575597377863220661233123392] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B3372, (.leaf 5 (Common.fact 430).pointIds 430), Tip3364_3374]
theorem treeEq3371 : B3371.tree = HexagonCover.NBand.M6667_6700.SplitData.node3371 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3372
  · rfl
  · rfl

def B3368 : Block := .branch 120 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664090166259977790681504959413600952778816] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B3369, (.leaf 5 (Common.fact 163).pointIds 163), B3371]
theorem treeEq3368 : B3368.tree = HexagonCover.NBand.M6667_6700.SplitData.node3368 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3369
  · rfl
  · exact treeEq3371

def B3462 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 5987772208144709921793202692030369005267807957942336] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1296).pointIds 1296)]
theorem treeEq3462 : B3462.tree = HexagonCover.NBand.M6667_6700.SplitData.node3462 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3461 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 5987772208144709921793202692030369005267807957942336] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3462, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1295).pointIds 1295)]
theorem treeEq3461 : B3461.tree = HexagonCover.NBand.M6667_6700.SplitData.node3461 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3462
  · rfl
  · rfl

def B3460 : Block := .branch 160 ![385, 1538, 75557863867751323408388, 29016580853992535015579656, 356811923176489970264571492362373784095784976, 393248, 5986310706507379018874999007197652722248152025399360] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1294).pointIds 1294), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3461]
theorem treeEq3460 : B3460.tree = HexagonCover.NBand.M6667_6700.SplitData.node3460 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3461

def B3367 : Block := .branch 47 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664090166259977790681504959413600952778816] ![(.leaf 0 (Common.fact 1262).pointIds 1262), B3368, B3460, (.leaf 3 (Common.fact 1263).pointIds 1263), (.leaf 4 (Common.fact 1264).pointIds 1264), (.leaf 5 (Common.fact 1265).pointIds 1265), (.leaf 6 (Common.fact 1266).pointIds 1266)]
theorem treeEq3367 : B3367.tree = HexagonCover.NBand.M6667_6700.SplitData.node3367 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3368
  · exact treeEq3460
  · rfl
  · rfl
  · rfl
  · rfl

def B3364 : Block := .branch 119 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3365, (.leaf 5 (Common.fact 419).pointIds 419), B3367]
theorem treeEq3364 : B3364.tree = HexagonCover.NBand.M6667_6700.SplitData.node3364 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3365
  · rfl
  · exact treeEq3367

theorem accepted3364 : B3364.accepted = true := by decide +kernel
theorem checked3364 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3364 (maskNeeds ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528]) := by
  rw [← treeEq3364]
  exact B3364.sound accepted3364
#print axioms checked3364

def Tip3362_3364 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3364 ![2596148429267414967186752771457409, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] checked3364
def B3466 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 5987772208144709258801163742564452072579309569048640] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 1298).pointIds 1298)]
theorem treeEq3466 : B3466.tree = HexagonCover.NBand.M6667_6700.SplitData.node3466 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3465 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 5987772208144709258801163742564452072579309569048640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3466, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1297).pointIds 1297)]
theorem treeEq3465 : B3465.tree = HexagonCover.NBand.M6667_6700.SplitData.node3465 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3466
  · rfl
  · rfl

def B3464 : Block := .branch 160 ![385, 1538, 80280230209883480266756, 29016580853992535015579656, 356811923176489970264571492362373784095784976, 393248, 5986310706507378355882960057731735789559653636505664] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1287).pointIds 1287), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3465]
theorem treeEq3464 : B3464.tree = HexagonCover.NBand.M6667_6700.SplitData.node3464 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3465

def B3470 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq3470 : B3470.tree = HexagonCover.NBand.M6667_6700.SplitData.node3470 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3469 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3470]
theorem treeEq3469 : B3469.tree = HexagonCover.NBand.M6667_6700.SplitData.node3469 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3470

def B3473 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq3473 : B3473.tree = HexagonCover.NBand.M6667_6700.SplitData.node3473 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3472 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3473]
theorem treeEq3472 : B3472.tree = HexagonCover.NBand.M6667_6700.SplitData.node3472 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3473

def B3471 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3472, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq3471 : B3471.tree = HexagonCover.NBand.M6667_6700.SplitData.node3471 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3472
  · rfl
  · rfl

def B3468 : Block := .branch 119 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3469, (.leaf 5 (Common.fact 419).pointIds 419), B3471]
theorem treeEq3468 : B3468.tree = HexagonCover.NBand.M6667_6700.SplitData.node3468 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3469
  · rfl
  · exact treeEq3471

def B3475 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq3475 : B3475.tree = HexagonCover.NBand.M6667_6700.SplitData.node3475 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3474 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3475, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq3474 : B3474.tree = HexagonCover.NBand.M6667_6700.SplitData.node3474 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3475
  · rfl
  · rfl

def B3467 : Block := .branch 112 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B3468, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B3474]
theorem treeEq3467 : B3467.tree = HexagonCover.NBand.M6667_6700.SplitData.node3467 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3468
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3474

def B3463 : Block := .branch 72 ![385, 1538, 75557863727013835053060, 29016580853992535015579656, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3464, B3467, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq3463 : B3463.tree = HexagonCover.NBand.M6667_6700.SplitData.node3463 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3464
  · exact treeEq3467
  · rfl
  · rfl
  · rfl

def B3363 : Block := .branch 111 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![Tip3362_3364, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B3463]
theorem treeEq3363 : B3363.tree = HexagonCover.NBand.M6667_6700.SplitData.node3363 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3463

def B3479 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892964684172901004342090038286745664] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1271).pointIds 1271)]
theorem treeEq3479 : B3479.tree = HexagonCover.NBand.M6667_6700.SplitData.node3479 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3478 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598844397538550267436026200824741952] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3479]
theorem treeEq3478 : B3478.tree = HexagonCover.NBand.M6667_6700.SplitData.node3478 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3479

def B3477 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374875169975376600142471753183974343158824907046976] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3478, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1270).pointIds 1270)]
theorem treeEq3477 : B3477.tree = HexagonCover.NBand.M6667_6700.SplitData.node3477 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3478
  · rfl
  · rfl

def B3476 : Block := .branch 159 ![385, 618970609938500496155215362, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148683369910767616201648996940775488] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 1269).pointIds 1269), (.leaf 2 (Common.fact 1250).pointIds 1250), (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B3477]
theorem treeEq3476 : B3476.tree = HexagonCover.NBand.M6667_6700.SplitData.node3476 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3477

def B3362 : Block := .branch 69 ![1152921504606847361, 618970019642690137449563650, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![B3363, B3476, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1011).pointIds 1011)]
theorem treeEq3362 : B3362.tree = HexagonCover.NBand.M6667_6700.SplitData.node3362 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3363
  · exact treeEq3476
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3362 : B3362.accepted = true := by decide +kernel
theorem checked3362 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3362 (maskNeeds ![1152921504606847361, 618970019642690137449563650, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528]) := by
  rw [← treeEq3362]
  exact B3362.sound accepted3362
#print axioms checked3362

end HexagonCover.NBand.M6667_6700.SplitTree.Run0047
