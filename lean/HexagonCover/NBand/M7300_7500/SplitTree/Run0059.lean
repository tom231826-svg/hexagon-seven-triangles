import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0050
import HexagonCover.NBand.M7300_7500.SplitTree.Run0051
import HexagonCover.NBand.M7300_7500.SplitTree.Run0052
import HexagonCover.NBand.M7300_7500.SplitTree.Run0053
import HexagonCover.NBand.M7300_7500.SplitTree.Run0055
import HexagonCover.NBand.M7300_7500.SplitTree.Run0058
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0059
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip3965_3973 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3973 ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0058.checked3973
def B4236 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq4236 : B4236.tree = HexagonCover.NBand.M7300_7500.SplitData.node4236 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4235 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B4236, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq4235 : B4235.tree = HexagonCover.NBand.M7300_7500.SplitData.node4235 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4236
  · rfl
  · rfl

def B4234 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 737869903685870421506, 18446745173221185540, 38687987410909568413229064, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1002).pointIds 1002), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4235]
theorem treeEq4234 : B4234.tree = HexagonCover.NBand.M7300_7500.SplitData.node4234 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4235

def B4233 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 737869903685870421506, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B4234, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq4233 : B4233.tree = HexagonCover.NBand.M7300_7500.SplitData.node4233 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4234
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4232 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 147574093327164769794, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B4233, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq4232 : B4232.tree = HexagonCover.NBand.M7300_7500.SplitData.node4232 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4233
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4231 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 147574093327164769794, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4232]
theorem treeEq4231 : B4231.tree = HexagonCover.NBand.M7300_7500.SplitData.node4231 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4232

def B4230 : Block := .branch 169 ![2475880078570760549798248833, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B4231, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq4230 : B4230.tree = HexagonCover.NBand.M7300_7500.SplitData.node4230 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4231
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4229 : Block := .branch 170 ![2475880078570760549798248833, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4230, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4229 : B4229.tree = HexagonCover.NBand.M7300_7500.SplitData.node4229 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4230
  · rfl

def B4228 : Block := .branch 171 ![2475880078570760549798248833, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4229, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq4228 : B4228.tree = HexagonCover.NBand.M7300_7500.SplitData.node4228 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4229
  · rfl
  · rfl

def B3972 : Block := .branch 68 ![10384596192949733827821542456689025, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip3965_3973, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B4228]
theorem treeEq3972 : B3972.tree = HexagonCover.NBand.M7300_7500.SplitData.node3972 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4228

def B3971 : Block := .branch 91 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B3972, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq3971 : B3971.tree = HexagonCover.NBand.M7300_7500.SplitData.node3971 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3972
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3970 : Block := .branch 113 ![385, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B3971, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq3970 : B3970.tree = HexagonCover.NBand.M7300_7500.SplitData.node3970 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3971
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3969 : Block := .branch 135 ![385, 147718208515240625666, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B3970, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq3969 : B3969.tree = HexagonCover.NBand.M7300_7500.SplitData.node3969 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3970
  · rfl

def B3968 : Block := .branch 138 ![385, 147718208515240625666, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B3969, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq3968 : B3968.tree = HexagonCover.NBand.M7300_7500.SplitData.node3968 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3969
  · rfl
  · rfl

def B3967 : Block := .branch 144 ![385, 147718208515240625666, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B3968, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq3967 : B3967.tree = HexagonCover.NBand.M7300_7500.SplitData.node3967 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3968
  · rfl

def B3966 : Block := .branch 149 ![385, 147718208515240625666, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B3967, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq3966 : B3966.tree = HexagonCover.NBand.M7300_7500.SplitData.node3966 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3967
  · rfl
  · rfl

def B3965 : Block := .branch 161 ![385, 147718208515240625666, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B3966]
theorem treeEq3965 : B3965.tree = HexagonCover.NBand.M7300_7500.SplitData.node3965 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3966

theorem accepted3965 : B3965.accepted = true := by decide +kernel
theorem checked3965 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3965 (maskNeeds ![385, 147718208515240625666, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq3965]
  exact B3965.sound accepted3965
#print axioms checked3965

def Tip3582_3588 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3588 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0051.checked3588
def Tip3582_3659 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3659 ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] HexagonCover.NBand.M7300_7500.SplitTree.Run0051.checked3659
def Tip3582_3693 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3693 ![385, 147718208515240625666, 18446745173221185540, 79266867029957937205715427336, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0052.checked3693
def Tip3582_3741 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3741 ![385, 147718208515240625666, 18446745173221185540, 79266857585224971466424999944, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0053.checked3741
def Tip3582_3821 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3821 ![385, 147718208515240625666, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0055.checked3821
def Tip3582_3965 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3965 ![385, 147718208515240625666, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 21778071483890954354332057599839810617408] checked3965
def B3658 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 890).pointIds 890), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq3658 : B3658.tree = HexagonCover.NBand.M7300_7500.SplitData.node3658 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3657 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B3658, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq3657 : B3657.tree = HexagonCover.NBand.M7300_7500.SplitData.node3657 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3658
  · rfl
  · rfl

def B3656 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B3657, (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq3656 : B3656.tree = HexagonCover.NBand.M7300_7500.SplitData.node3656 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3657
  · rfl

def B3655 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![B3656, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq3655 : B3655.tree = HexagonCover.NBand.M7300_7500.SplitData.node3655 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3656
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3654 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3655]
theorem treeEq3654 : B3654.tree = HexagonCover.NBand.M7300_7500.SplitData.node3654 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3655

def B3653 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![B3654, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq3653 : B3653.tree = HexagonCover.NBand.M7300_7500.SplitData.node3653 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3654
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3652 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954656563512503497104293952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3653, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3652 : B3652.tree = HexagonCover.NBand.M7300_7500.SplitData.node3652 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3653
  · rfl

def B3651 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954656563512503497104293952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3652, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq3651 : B3651.tree = HexagonCover.NBand.M7300_7500.SplitData.node3651 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3652
  · rfl
  · rfl

def B3587 : Block := .branch 78 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip3582_3588, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3651]
theorem treeEq3587 : B3587.tree = HexagonCover.NBand.M7300_7500.SplitData.node3587 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3651

def B3586 : Block := .branch 76 ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B3587, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip3582_3659]
theorem treeEq3586 : B3586.tree = HexagonCover.NBand.M7300_7500.SplitData.node3586 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3587
  · rfl
  · rfl
  · rfl
  · rfl

def B3585 : Block := .branch 74 ![385, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), B3586, Tip3582_3693, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3585 : B3585.tree = HexagonCover.NBand.M7300_7500.SplitData.node3585 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3586
  · rfl
  · rfl
  · rfl
  · rfl

def B3584 : Block := .branch 73 ![385, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), B3585, Tip3582_3741, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq3584 : B3584.tree = HexagonCover.NBand.M7300_7500.SplitData.node3584 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3585
  · rfl
  · rfl
  · rfl
  · rfl

def B3583 : Block := .branch 72 ![385, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B3584, Tip3582_3821, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq3583 : B3583.tree = HexagonCover.NBand.M7300_7500.SplitData.node3583 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3584
  · rfl
  · rfl
  · rfl
  · rfl

def B3582 : Block := .branch 71 ![385, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), B3583, Tip3582_3965, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq3582 : B3582.tree = HexagonCover.NBand.M7300_7500.SplitData.node3582 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3583
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3582 : B3582.accepted = true := by decide +kernel
theorem checked3582 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3582 (maskNeeds ![385, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq3582]
  exact B3582.sound accepted3582
#print axioms checked3582

def Tip3580_3582 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3582 ![385, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked3582
def B4243 : Block := .branch 125 ![1122433257470133441180429951526105359095756193005953, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 981).pointIds 981)]
theorem treeEq4243 : B4243.tree = HexagonCover.NBand.M7300_7500.SplitData.node4243 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4242 : Block := .branch 168 ![748288838313422294120286634350736906063837462004097, 590440066284269864450, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B4243, (.leaf 1 (Common.fact 1010).pointIds 1010), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq4242 : B4242.tree = HexagonCover.NBand.M7300_7500.SplitData.node4242 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4243
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4241 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 753).pointIds 753), B4242, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq4241 : B4241.tree = HexagonCover.NBand.M7300_7500.SplitData.node4241 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4242
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4240 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4241]
theorem treeEq4240 : B4240.tree = HexagonCover.NBand.M7300_7500.SplitData.node4240 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4241

def B4239 : Block := .branch 169 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B4240, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 980).pointIds 980)]
theorem treeEq4239 : B4239.tree = HexagonCover.NBand.M7300_7500.SplitData.node4239 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4240
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4238 : Block := .branch 170 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4239, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4238 : B4238.tree = HexagonCover.NBand.M7300_7500.SplitData.node4238 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4239
  · rfl

def B4237 : Block := .branch 171 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4238, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq4237 : B4237.tree = HexagonCover.NBand.M7300_7500.SplitData.node4237 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4238
  · rfl
  · rfl

def B3581 : Block := .branch 67 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 198).pointIds 198), Tip3580_3582, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B4237]
theorem treeEq3581 : B3581.tree = HexagonCover.NBand.M7300_7500.SplitData.node3581 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4237

def B4249 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 983).pointIds 983), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq4249 : B4249.tree = HexagonCover.NBand.M7300_7500.SplitData.node4249 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4248 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B4249, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq4248 : B4248.tree = HexagonCover.NBand.M7300_7500.SplitData.node4248 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4249
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4247 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4248]
theorem treeEq4247 : B4247.tree = HexagonCover.NBand.M7300_7500.SplitData.node4247 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4248

def B4246 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974311749925714704515727424] ![B4247, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 982).pointIds 982)]
theorem treeEq4246 : B4246.tree = HexagonCover.NBand.M7300_7500.SplitData.node4246 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4245 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4246, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4245 : B4245.tree = HexagonCover.NBand.M7300_7500.SplitData.node4245 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4246
  · rfl

def B4244 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4245, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4244 : B4244.tree = HexagonCover.NBand.M7300_7500.SplitData.node4244 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4245
  · rfl
  · rfl

def B3580 : Block := .branch 65 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B3581, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B4244]
theorem treeEq3580 : B3580.tree = HexagonCover.NBand.M7300_7500.SplitData.node3580 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3581
  · rfl
  · rfl
  · rfl
  · exact treeEq4244

theorem accepted3580 : B3580.accepted = true := by decide +kernel
theorem checked3580 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3580 (maskNeeds ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq3580]
  exact B3580.sound accepted3580
#print axioms checked3580

def Tip3569_3580 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3580 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked3580
def B3579 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072528559109803447333728274579038142528] ![(.leaf 0 (Common.fact 994).pointIds 994), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 995).pointIds 995)]
theorem treeEq3579 : B3579.tree = HexagonCover.NBand.M7300_7500.SplitData.node3579 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3578 : Block := .branch 170 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 393248, 23384026219072528559743628747447842975327389745216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3579, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3578 : B3578.tree = HexagonCover.NBand.M7300_7500.SplitData.node3578 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3579
  · rfl

def B3577 : Block := .branch 171 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219072528559743628747447842975327389745216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3578, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 993).pointIds 993)]
theorem treeEq3577 : B3577.tree = HexagonCover.NBand.M7300_7500.SplitData.node3577 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3578
  · rfl
  · rfl

def B3576 : Block := .branch 113 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219072518175149911677792585914334731305024] ![(.leaf 0 (Common.fact 992).pointIds 992), (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), B3577]
theorem treeEq3576 : B3576.tree = HexagonCover.NBand.M7300_7500.SplitData.node3576 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3577

def B3575 : Block := .branch 65 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B3576, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq3575 : B3575.tree = HexagonCover.NBand.M7300_7500.SplitData.node3575 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3576
  · rfl
  · rfl
  · rfl
  · rfl

def B3574 : Block := .branch 67 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 198).pointIds 198), B3575, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq3574 : B3574.tree = HexagonCover.NBand.M7300_7500.SplitData.node3574 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3575
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3573 : Block := .branch 138 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B3574, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq3573 : B3573.tree = HexagonCover.NBand.M7300_7500.SplitData.node3573 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3574
  · rfl
  · rfl

def B3572 : Block := .branch 144 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B3573, (.leaf 6 (Common.fact 984).pointIds 984)]
theorem treeEq3572 : B3572.tree = HexagonCover.NBand.M7300_7500.SplitData.node3572 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3573
  · rfl

def B3571 : Block := .branch 124 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219072518175149911677792585914334731305024] ![(.leaf 0 (Common.fact 991).pointIds 991), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B3572]
theorem treeEq3571 : B3571.tree = HexagonCover.NBand.M7300_7500.SplitData.node3571 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3572

def B3570 : Block := .branch 164 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 990).pointIds 990), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3571]
theorem treeEq3570 : B3570.tree = HexagonCover.NBand.M7300_7500.SplitData.node3570 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3571

def B3569 : Block := .branch 59 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B3570, Tip3569_3580, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq3569 : B3569.tree = HexagonCover.NBand.M7300_7500.SplitData.node3569 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3570
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3569 : B3569.accepted = true := by decide +kernel
theorem checked3569 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3569 (maskNeeds ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq3569]
  exact B3569.sound accepted3569
#print axioms checked3569

def Tip2911_2915 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2915 ![385, 216313519602140674, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0050.checked2915
def Tip2911_3569 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3569 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked3569
def B2914 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 935).pointIds 935)]
theorem treeEq2914 : B2914.tree = HexagonCover.NBand.M7300_7500.SplitData.node2914 := by
  change Tree.branch (102 : Fin 172) _ = Tree.branch (102 : Fin 172) _
  apply congrArg (Tree.branch (102 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2913 : Block := .branch 168 ![288230376151712129, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2914]
theorem treeEq2913 : B2913.tree = HexagonCover.NBand.M7300_7500.SplitData.node2913 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2914

def B2912 : Block := .branch 58 ![385, 216313519602140674, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B2913, Tip2911_2915, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq2912 : B2912.tree = HexagonCover.NBand.M7300_7500.SplitData.node2912 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2913
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3568 : Block := .branch 91 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 2993155353275488515612970050411246142768154144145472] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 989).pointIds 989)]
theorem treeEq3568 : B3568.tree = HexagonCover.NBand.M7300_7500.SplitData.node3568 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3567 : Block := .branch 171 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496577676975293731967614255287969410137805572636688, 393248, 21799339131823513008298518512804296130624] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 965).pointIds 965), (.leaf 5 (Common.fact 656).pointIds 656), B3568]
theorem treeEq3567 : B3567.tree = HexagonCover.NBand.M7300_7500.SplitData.node3567 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3568

def B3566 : Block := .branch 170 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 21799339131823513008298518512804296130624] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3567, (.leaf 5 (Common.fact 988).pointIds 988), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3566 : B3566.tree = HexagonCover.NBand.M7300_7500.SplitData.node3566 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3567
  · rfl
  · rfl

def B3565 : Block := .branch 114 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131823513008298518512804296130624] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 233).pointIds 233), (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), B3566, (.leaf 6 (Common.fact 237).pointIds 237)]
theorem treeEq3565 : B3565.tree = HexagonCover.NBand.M7300_7500.SplitData.node3565 := by
  change Tree.branch (114 : Fin 172) _ = Tree.branch (114 : Fin 172) _
  apply congrArg (Tree.branch (114 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3566
  · rfl

def B3564 : Block := .branch 65 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B3565, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq3564 : B3564.tree = HexagonCover.NBand.M7300_7500.SplitData.node3564 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3565
  · rfl
  · rfl
  · rfl
  · rfl

def B3563 : Block := .branch 67 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 198).pointIds 198), B3564, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq3563 : B3563.tree = HexagonCover.NBand.M7300_7500.SplitData.node3563 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3564
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3562 : Block := .branch 138 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B3563, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq3562 : B3562.tree = HexagonCover.NBand.M7300_7500.SplitData.node3562 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3563
  · rfl
  · rfl

def B3561 : Block := .branch 144 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B3562, (.leaf 6 (Common.fact 984).pointIds 984)]
theorem treeEq3561 : B3561.tree = HexagonCover.NBand.M7300_7500.SplitData.node3561 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3562
  · rfl

def B3560 : Block := .branch 124 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219072518175149911677792585914334731305024] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B3561]
theorem treeEq3560 : B3560.tree = HexagonCover.NBand.M7300_7500.SplitData.node3560 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3561

def B3559 : Block := .branch 164 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 163).pointIds 163), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3560]
theorem treeEq3559 : B3559.tree = HexagonCover.NBand.M7300_7500.SplitData.node3559 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3560

def B3558 : Block := .branch 58 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B3559, Tip2911_3569, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq3558 : B3558.tree = HexagonCover.NBand.M7300_7500.SplitData.node3558 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3559
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2911 : Block := .branch 56 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 153).pointIds 153), B2912, B3558, (.leaf 3 (Common.fact 154).pointIds 154), (.leaf 4 (Common.fact 155).pointIds 155), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 157).pointIds 157)]
theorem treeEq2911 : B2911.tree = HexagonCover.NBand.M7300_7500.SplitData.node2911 := by
  change Tree.branch (56 : Fin 172) _ = Tree.branch (56 : Fin 172) _
  apply congrArg (Tree.branch (56 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2912
  · exact treeEq3558
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2911 : B2911.accepted = true := by decide +kernel
theorem checked2911 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2911 (maskNeeds ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq2911]
  exact B2911.sound accepted2911
#print axioms checked2911

end HexagonCover.NBand.M7300_7500.SplitTree.Run0059
