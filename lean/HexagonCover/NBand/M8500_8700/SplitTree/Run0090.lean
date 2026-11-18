import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0086
import HexagonCover.NBand.M8500_8700.SplitTree.Run0087
import HexagonCover.NBand.M8500_8700.SplitTree.Run0088
import HexagonCover.NBand.M8500_8700.SplitTree.Run0089
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0090
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip6289_6292 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6292 ![1856910354075975591701512577, 151115729774546960516610, 48394811716448124149962756, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0088.checked6292
def Tip6289_6379 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6379 ![1237940334433285454251950465, 151115729774546960516610, 48394811716448124149962756, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0089.checked6379
def B6377 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6377 : B6377.tree = HexagonCover.NBand.M8500_8700.SplitData.node6377 := by
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

def B6376 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6377, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6376 : B6376.tree = HexagonCover.NBand.M8500_8700.SplitData.node6376 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6377
  · rfl

def B6375 : Block := .branch 163 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B6376]
theorem treeEq6375 : B6375.tree = HexagonCover.NBand.M8500_8700.SplitData.node6375 := by
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
  · exact treeEq6376

def B6374 : Block := .branch 165 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B6375, (.leaf 0 [] 0)]
theorem treeEq6374 : B6374.tree = HexagonCover.NBand.M8500_8700.SplitData.node6374 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6375
  · rfl

def B6373 : Block := .branch 167 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B6374, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6373 : B6373.tree = HexagonCover.NBand.M8500_8700.SplitData.node6373 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6374
  · rfl

def B6291 : Block := .branch 98 ![1856910354075975591701512577, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), Tip6289_6292, B6373, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6291 : B6291.tree = HexagonCover.NBand.M8500_8700.SplitData.node6291 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6373
  · rfl
  · rfl

def B6464 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6464 : B6464.tree = HexagonCover.NBand.M8500_8700.SplitData.node6464 := by
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

def B6463 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6464, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6463 : B6463.tree = HexagonCover.NBand.M8500_8700.SplitData.node6463 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6464
  · rfl

def B6462 : Block := .branch 163 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B6463]
theorem treeEq6462 : B6462.tree = HexagonCover.NBand.M8500_8700.SplitData.node6462 := by
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
  · exact treeEq6463

def B6461 : Block := .branch 165 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B6462, (.leaf 0 [] 0)]
theorem treeEq6461 : B6461.tree = HexagonCover.NBand.M8500_8700.SplitData.node6461 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6462
  · rfl

def B6460 : Block := .branch 167 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B6461, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6460 : B6460.tree = HexagonCover.NBand.M8500_8700.SplitData.node6460 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6461
  · rfl

def B6378 : Block := .branch 98 ![1237940334433285454251950465, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), Tip6289_6379, B6460, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6378 : B6378.tree = HexagonCover.NBand.M8500_8700.SplitData.node6378 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6460
  · rfl
  · rfl

def B6290 : Block := .branch 89 ![1237940334433285454251950465, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B6291, B6378, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6290 : B6290.tree = HexagonCover.NBand.M8500_8700.SplitData.node6290 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6291
  · exact treeEq6378
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6467 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6467 : B6467.tree = HexagonCover.NBand.M8500_8700.SplitData.node6467 := by
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

def B6466 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6467, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6466 : B6466.tree = HexagonCover.NBand.M8500_8700.SplitData.node6466 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6467
  · rfl

def B6465 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158538531984262469970967945224, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6466]
theorem treeEq6465 : B6465.tree = HexagonCover.NBand.M8500_8700.SplitData.node6465 := by
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
  · exact treeEq6466

def B6289 : Block := .branch 86 ![1237940334433285454251950465, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B6290, B6465, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq6289 : B6289.tree = HexagonCover.NBand.M8500_8700.SplitData.node6289 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6290
  · exact treeEq6465
  · rfl
  · rfl
  · rfl

theorem accepted6289 : B6289.accepted = true := by decide +kernel
theorem checked6289 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6289 (maskNeeds ![1237940334433285454251950465, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6289]
  exact B6289.sound accepted6289
#print axioms checked6289

def Tip6193_6197 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6197 ![1237940334433285454251950465, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0087.checked6197
def B6276 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6276 : B6276.tree = HexagonCover.NBand.M8500_8700.SplitData.node6276 := by
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

def B6275 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6276, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6275 : B6275.tree = HexagonCover.NBand.M8500_8700.SplitData.node6275 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6276
  · rfl

def B6274 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6275]
theorem treeEq6274 : B6274.tree = HexagonCover.NBand.M8500_8700.SplitData.node6274 := by
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
  · exact treeEq6275

def B6196 : Block := .branch 86 ![1237940334433285454251950465, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), Tip6193_6197, B6274, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq6196 : B6196.tree = HexagonCover.NBand.M8500_8700.SplitData.node6196 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6274
  · rfl
  · rfl
  · rfl

def B6279 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6279 : B6279.tree = HexagonCover.NBand.M8500_8700.SplitData.node6279 := by
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

def B6278 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6279, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6278 : B6278.tree = HexagonCover.NBand.M8500_8700.SplitData.node6278 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6279
  · rfl

def B6277 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6278]
theorem treeEq6277 : B6277.tree = HexagonCover.NBand.M8500_8700.SplitData.node6277 := by
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
  · exact treeEq6278

def B6195 : Block := .branch 85 ![1237940334433285454251950465, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B6196, B6277, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq6195 : B6195.tree = HexagonCover.NBand.M8500_8700.SplitData.node6195 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6196
  · exact treeEq6277
  · rfl
  · rfl
  · rfl

def B6282 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6282 : B6282.tree = HexagonCover.NBand.M8500_8700.SplitData.node6282 := by
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

def B6281 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6282, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6281 : B6281.tree = HexagonCover.NBand.M8500_8700.SplitData.node6281 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6282
  · rfl

def B6280 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6281]
theorem treeEq6280 : B6280.tree = HexagonCover.NBand.M8500_8700.SplitData.node6280 := by
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
  · exact treeEq6281

def B6194 : Block := .branch 84 ![1237940334433285454251950465, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B6195, B6280, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq6194 : B6194.tree = HexagonCover.NBand.M8500_8700.SplitData.node6194 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6195
  · exact treeEq6280
  · rfl
  · rfl
  · rfl

def B6285 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6285 : B6285.tree = HexagonCover.NBand.M8500_8700.SplitData.node6285 := by
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

def B6284 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6285, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6284 : B6284.tree = HexagonCover.NBand.M8500_8700.SplitData.node6284 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6285
  · rfl

def B6283 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6284]
theorem treeEq6283 : B6283.tree = HexagonCover.NBand.M8500_8700.SplitData.node6283 := by
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
  · exact treeEq6284

def B6193 : Block := .branch 83 ![1237940334433285454251950465, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B6194, B6283, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq6193 : B6193.tree = HexagonCover.NBand.M8500_8700.SplitData.node6193 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6194
  · exact treeEq6283
  · rfl
  · rfl
  · rfl

theorem accepted6193 : B6193.accepted = true := by decide +kernel
theorem checked6193 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6193 (maskNeeds ![1237940334433285454251950465, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq6193]
  exact B6193.sound accepted6193
#print axioms checked6193

def Tip5907_6004 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6004 ![1238242565888189111545627009, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0086.checked6004
def Tip5907_5908 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5908 ![1238242565888189111545627009, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0086.checked5908
def B6185 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6185 : B6185.tree = HexagonCover.NBand.M8500_8700.SplitData.node6185 := by
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

def B6184 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6185, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6184 : B6184.tree = HexagonCover.NBand.M8500_8700.SplitData.node6184 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6185
  · rfl

def B6183 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6184]
theorem treeEq6183 : B6183.tree = HexagonCover.NBand.M8500_8700.SplitData.node6183 := by
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
  · exact treeEq6184

def B6003 : Block := .branch 85 ![1238242565888189111545627009, 151115729774546960516610, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), Tip5907_6004, B6183, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq6003 : B6003.tree = HexagonCover.NBand.M8500_8700.SplitData.node6003 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6183
  · rfl
  · rfl
  · rfl

def B6188 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6188 : B6188.tree = HexagonCover.NBand.M8500_8700.SplitData.node6188 := by
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

def B6187 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6188, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6187 : B6187.tree = HexagonCover.NBand.M8500_8700.SplitData.node6187 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6188
  · rfl

def B6186 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6187]
theorem treeEq6186 : B6186.tree = HexagonCover.NBand.M8500_8700.SplitData.node6186 := by
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
  · exact treeEq6187

def B6002 : Block := .branch 84 ![1238242565888189111545627009, 151115729774546960516610, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B6003, B6186, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq6002 : B6002.tree = HexagonCover.NBand.M8500_8700.SplitData.node6002 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6003
  · exact treeEq6186
  · rfl
  · rfl
  · rfl

def B6191 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6191 : B6191.tree = HexagonCover.NBand.M8500_8700.SplitData.node6191 := by
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

def B6190 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6191, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6190 : B6190.tree = HexagonCover.NBand.M8500_8700.SplitData.node6190 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6191
  · rfl

def B6189 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6190]
theorem treeEq6189 : B6189.tree = HexagonCover.NBand.M8500_8700.SplitData.node6189 := by
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
  · exact treeEq6190

def B6001 : Block := .branch 83 ![1238242565888189111545627009, 151115729774546960516610, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B6002, B6189, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq6001 : B6001.tree = HexagonCover.NBand.M8500_8700.SplitData.node6001 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6002
  · exact treeEq6189
  · rfl
  · rfl
  · rfl

def B5907 : Block := .branch 82 ![1238242565888189111545627009, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), Tip5907_5908, B6001, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq5907 : B5907.tree = HexagonCover.NBand.M8500_8700.SplitData.node5907 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6001
  · rfl
  · rfl
  · rfl

theorem accepted5907 : B5907.accepted = true := by decide +kernel
theorem checked5907 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5907 (maskNeeds ![1238242565888189111545627009, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq5907]
  exact B5907.sound accepted5907
#print axioms checked5907

def B6498 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq6498 : B6498.tree = HexagonCover.NBand.M8500_8700.SplitData.node6498 := by
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

def B6497 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6498, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq6497 : B6497.tree = HexagonCover.NBand.M8500_8700.SplitData.node6497 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6498
  · rfl

def B6496 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6497]
theorem treeEq6496 : B6496.tree = HexagonCover.NBand.M8500_8700.SplitData.node6496 := by
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
  · exact treeEq6497

def B6495 : Block := .branch 172 ![1238242270740283932192801153, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6496, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq6495 : B6495.tree = HexagonCover.NBand.M8500_8700.SplitData.node6495 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6496
  · rfl
  · rfl
  · rfl

def B6494 : Block := .branch 159 ![5192298715747118011504565971583361, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 998).pointIds 998), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6495]
theorem treeEq6494 : B6494.tree = HexagonCover.NBand.M8500_8700.SplitData.node6494 := by
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
  · exact treeEq6495

def B6504 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq6504 : B6504.tree = HexagonCover.NBand.M8500_8700.SplitData.node6504 := by
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

def B6503 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6504, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq6503 : B6503.tree = HexagonCover.NBand.M8500_8700.SplitData.node6503 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6504
  · rfl

def B6502 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6503]
theorem treeEq6502 : B6502.tree = HexagonCover.NBand.M8500_8700.SplitData.node6502 := by
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
  · exact treeEq6503

def B6501 : Block := .branch 172 ![1238242270740283932192801153, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6502, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq6501 : B6501.tree = HexagonCover.NBand.M8500_8700.SplitData.node6501 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6502
  · rfl
  · rfl
  · rfl

def B6500 : Block := .branch 159 ![10385863224882173869436559004008833, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 1000).pointIds 1000), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6501]
theorem treeEq6500 : B6500.tree = HexagonCover.NBand.M8500_8700.SplitData.node6500 := by
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
  · exact treeEq6501

def B6508 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq6508 : B6508.tree = HexagonCover.NBand.M8500_8700.SplitData.node6508 := by
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

def B6507 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6508, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq6507 : B6507.tree = HexagonCover.NBand.M8500_8700.SplitData.node6507 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6508
  · rfl

def B6506 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6507]
theorem treeEq6506 : B6506.tree = HexagonCover.NBand.M8500_8700.SplitData.node6506 := by
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
  · exact treeEq6507

def B6505 : Block := .branch 172 ![1238242270740283932192801153, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6506, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq6505 : B6505.tree = HexagonCover.NBand.M8500_8700.SplitData.node6505 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6506
  · rfl
  · rfl
  · rfl

def B6499 : Block := .branch 113 ![1269507812518612375566345568641, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B6500, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B6505]
theorem treeEq6499 : B6499.tree = HexagonCover.NBand.M8500_8700.SplitData.node6499 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6500
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6505

def B6493 : Block := .branch 112 ![1269507812518612375566345568641, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B6494, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B6499]
theorem treeEq6493 : B6493.tree = HexagonCover.NBand.M8500_8700.SplitData.node6493 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6494
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6499

def B6510 : Block := .branch 168 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 978).pointIds 978), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq6510 : B6510.tree = HexagonCover.NBand.M8500_8700.SplitData.node6510 := by
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

def B6509 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6510, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq6509 : B6509.tree = HexagonCover.NBand.M8500_8700.SplitData.node6509 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6510
  · rfl

def B6492 : Block := .branch 109 ![1269507812518612375566345568641, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B6493, (.leaf 5 (Common.fact 294).pointIds 294), B6509]
theorem treeEq6492 : B6492.tree = HexagonCover.NBand.M8500_8700.SplitData.node6492 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6493
  · rfl
  · exact treeEq6509

theorem accepted6492 : B6492.accepted = true := by decide +kernel
theorem checked6492 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6492 (maskNeeds ![1269507812518612375566345568641, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq6492]
  exact B6492.sound accepted6492
#print axioms checked6492

end HexagonCover.NBand.M8500_8700.SplitTree.Run0090
