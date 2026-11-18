import HexagonCover.N7900.SplitAlignedTree.Run0011
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0012
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip0890_0908 : Block := .tip HexagonCover.N7900.SplitData.node0908 ![10143680682494701782882129543553, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] HexagonCover.N7900.SplitAlignedTree.Run0011.checked0908
def Tip0890_0891 : Block := .tip HexagonCover.N7900.SplitData.node0891 ![10141204801825835211973625643393, 309485010542061746592417282, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0011.checked0891
def B0970 : Block := .branch 142 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 1461512809502841314707419188838393916442428309568] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 630).pointIds 630), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0970 : B0970.tree = HexagonCover.N7900.SplitData.node0970 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0969 : Block := .branch 160 ![385, 604610483900641752122882, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 393248, 11172171938396503734356122110896786495766592] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 629).pointIds 629), (.leaf 2 (Common.fact 596).pointIds 596), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), B0970]
theorem treeEq0969 : B0969.tree = HexagonCover.N7900.SplitData.node0969 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0970

def B0968 : Block := .branch 79 ![42535295865117308523217636287676678529, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 393248, 11172171938396503734356122110896786495766592] ![(.leaf 0 (Common.fact 627).pointIds 627), B0969, (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), (.leaf 6 (Common.fact 628).pointIds 628)]
theorem treeEq0968 : B0968.tree = HexagonCover.N7900.SplitData.node0968 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0969
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0967 : Block := .branch 161 ![42535295865117308523217636287676678529, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 393248, 11172171938396503734356122110896786495766592] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 625).pointIds 625), B0968, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 626).pointIds 626)]
theorem treeEq0967 : B0967.tree = HexagonCover.N7900.SplitData.node0967 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0968
  · rfl
  · rfl
  · rfl

def B0966 : Block := .branch 143 ![42535295865117308523217636287676678529, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21799339131192163588262974572605742776384] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 122).pointIds 122), B0967]
theorem treeEq0966 : B0966.tree = HexagonCover.N7900.SplitData.node0966 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0967

def B0965 : Block := .branch 124 ![42535295865117308523217636287676678529, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 623).pointIds 623), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0966]
theorem treeEq0965 : B0965.tree = HexagonCover.N7900.SplitData.node0965 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0966

def B0964 : Block := .branch 125 ![590295810358705652097, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 748288838313422294120286634350736906063837462396960, 21778071483259914419306335004709982044224] ![B0965, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq0964 : B0964.tree = HexagonCover.N7900.SplitData.node0964 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0965
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0963 : Block := .branch 157 ![590295810358705652097, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 748288838313422294120286634350736906063837462396960, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B0964, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq0963 : B0963.tree = HexagonCover.N7900.SplitData.node0963 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0964
  · rfl
  · rfl

def B0962 : Block := .branch 76 ![590295810358705652097, 442721998506517595650, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 748288838313422294120286634350736906063837462396960, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B0963, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0962 : B0962.tree = HexagonCover.N7900.SplitData.node0962 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0963
  · rfl
  · rfl
  · rfl
  · rfl

def B0961 : Block := .branch 68 ![93536104789177786765035829294432409068338388402561, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 748288838313422294120286634350736906063837462396960, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 620).pointIds 620), B0962, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0961 : B0961.tree = HexagonCover.N7900.SplitData.node0961 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0962
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0960 : Block := .branch 166 ![590295810358705652097, 147574093327164769794, 9295429630892709892, 24584, 11692013098647223345629478661730264157247460442128, 748288838313422294120286634350736906063837462396960, 21778071483259914419306335004709982044224] ![B0961, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0960 : B0960.tree = HexagonCover.N7900.SplitData.node0960 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0961
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0959 : Block := .branch 169 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 11692013098647223345629478661730264157247460442128, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 559).pointIds 559), B0960, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0959 : B0959.tree = HexagonCover.N7900.SplitData.node0959 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0960
  · rfl

def B0958 : Block := .branch 163 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B0959, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq0958 : B0958.tree = HexagonCover.N7900.SplitData.node0958 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0959
  · rfl
  · rfl

def B0907 : Block := .branch 91 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![Tip0890_0908, (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B0958]
theorem treeEq0907 : B0907.tree = HexagonCover.N7900.SplitData.node0907 := by
  change Tree.branch (91 : Fin 170) _ = Tree.branch (91 : Fin 170) _
  apply congrArg (Tree.branch (91 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0958

def B0890 : Block := .branch 88 ![10141204802416131022332331295105, 148294669267544049154, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 88).pointIds 88), Tip0890_0891, (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0907]
theorem treeEq0890 : B0890.tree = HexagonCover.N7900.SplitData.node0890 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0907

theorem accepted0890 : B0890.accepted = true := by decide +kernel
theorem checked0890 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0890 (maskNeeds ![10141204802416131022332331295105, 148294669267544049154, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0890]
  exact B0890.sound accepted0890
#print axioms checked0890

def B0997 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq0997 : B0997.tree = HexagonCover.N7900.SplitData.node0997 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0996 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0997]
theorem treeEq0996 : B0996.tree = HexagonCover.N7900.SplitData.node0996 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0997

def B0995 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B0996, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0995 : B0995.tree = HexagonCover.N7900.SplitData.node0995 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0996
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0994 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B0995, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq0994 : B0994.tree = HexagonCover.N7900.SplitData.node0994 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0995
  · rfl
  · rfl

def B0993 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B0994, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0993 : B0993.tree = HexagonCover.N7900.SplitData.node0993 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0994
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0992 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B0993, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0992 : B0992.tree = HexagonCover.N7900.SplitData.node0992 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0993
  · rfl

def B0991 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0992, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0991 : B0991.tree = HexagonCover.N7900.SplitData.node0991 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0992
  · rfl
  · rfl

def B0990 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0991]
theorem treeEq0990 : B0990.tree = HexagonCover.N7900.SplitData.node0990 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0991

def B0999 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0999 : B0999.tree = HexagonCover.N7900.SplitData.node0999 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0998 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0999, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0998 : B0998.tree = HexagonCover.N7900.SplitData.node0998 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0999
  · rfl
  · rfl

def B0989 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B0990, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0998]
theorem treeEq0989 : B0989.tree = HexagonCover.N7900.SplitData.node0989 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0990
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0998

def B1006 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1006 : B1006.tree = HexagonCover.N7900.SplitData.node1006 := by
  change Tree.branch (100 : Fin 170) _ = Tree.branch (100 : Fin 170) _
  apply congrArg (Tree.branch (100 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1005 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1006]
theorem treeEq1005 : B1005.tree = HexagonCover.N7900.SplitData.node1005 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1006

def B1004 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1005, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1004 : B1004.tree = HexagonCover.N7900.SplitData.node1004 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1005
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1003 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1004, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1003 : B1003.tree = HexagonCover.N7900.SplitData.node1003 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1004
  · rfl
  · rfl

def B1002 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1003, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1002 : B1002.tree = HexagonCover.N7900.SplitData.node1002 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1003
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1001 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1002, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1001 : B1001.tree = HexagonCover.N7900.SplitData.node1001 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1002
  · rfl

def B1000 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1001, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1000 : B1000.tree = HexagonCover.N7900.SplitData.node1000 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1001
  · rfl
  · rfl

def B0988 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B0989, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1000]
theorem treeEq0988 : B0988.tree = HexagonCover.N7900.SplitData.node0988 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0989
  · rfl
  · rfl
  · rfl
  · exact treeEq1000

theorem accepted0988 : B0988.accepted = true := by decide +kernel
theorem checked0988 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0988 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0988]
  exact B0988.sound accepted0988
#print axioms checked0988

def Tip0889_0890 : Block := .tip HexagonCover.N7900.SplitData.node0890 ![10141204802416131022332331295105, 148294669267544049154, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0890
def B0983 : Block := .branch 125 ![467680523945888933825179146469210566289898413752705, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 654).pointIds 654), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq0983 : B0983.tree = HexagonCover.N7900.SplitData.node0983 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0982 : Block := .branch 168 ![93536104789177786765035829293842113257979682750849, 1461501637330902918203684833011430924835285370370, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 27222589354626047140998506655015283195968] ![B0983, (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 591).pointIds 591), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq0982 : B0982.tree = HexagonCover.N7900.SplitData.node0982 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0983
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0981 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 295147905179352827394, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 27222589354626047140998506655015283195968] ![(.leaf 0 (Common.fact 334).pointIds 334), B0982, (.leaf 2 (Common.fact 596).pointIds 596), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0981 : B0981.tree = HexagonCover.N7900.SplitData.node0981 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0982
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0980 : Block := .branch 132 ![93536104789177786765035829293842113257979682750849, 295147905179352827394, 9295429630892709892, 38685626227668133590622216, 1431080633286957331910737421027606573516685328, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 177).pointIds 177), B0981]
theorem treeEq0980 : B0980.tree = HexagonCover.N7900.SplitData.node0980 := by
  change Tree.branch (132 : Fin 170) _ = Tree.branch (132 : Fin 170) _
  apply congrArg (Tree.branch (132 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0981

def B0979 : Block := .branch 138 ![93536104789177786765035829293842113257979682750849, 295147905179352827394, 9295429630892709892, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0980, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0979 : B0979.tree = HexagonCover.N7900.SplitData.node0979 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0980
  · rfl
  · rfl

def B0978 : Block := .branch 68 ![93536104789177786765035829294432409068338388402561, 1538, 9295429630892709892, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 748294547304193117959810867494614704044382993383456, 32667107225361062556412500373923574579264] ![(.leaf 0 (Common.fact 620).pointIds 620), B0979, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0978 : B0978.tree = HexagonCover.N7900.SplitData.node0978 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0979
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0977 : Block := .branch 133 ![93536104789177786765035829294432409068338388402561, 1538, 9295429630892709892, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 647).pointIds 647), (.leaf 5 (Common.fact 164).pointIds 164), B0978]
theorem treeEq0977 : B0977.tree = HexagonCover.N7900.SplitData.node0977 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0978

def B0976 : Block := .branch 139 ![93536104789177786765035829294432409068338388402561, 1538, 9295429630892709892, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 641).pointIds 641), (.leaf 1 (Common.fact 642).pointIds 642), (.leaf 2 (Common.fact 643).pointIds 643), (.leaf 3 (Common.fact 644).pointIds 644), B0977, (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0976 : B0976.tree = HexagonCover.N7900.SplitData.node0976 := by
  change Tree.branch (139 : Fin 170) _ = Tree.branch (139 : Fin 170) _
  apply congrArg (Tree.branch (139 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0977
  · rfl
  · rfl

def B0975 : Block := .branch 99 ![93536104789177786765035829294432409068338388402561, 1538, 9295429630892709892, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 748294547304193117959810867494614704044382993383456, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 635).pointIds 635), (.leaf 1 (Common.fact 636).pointIds 636), (.leaf 2 (Common.fact 637).pointIds 637), (.leaf 3 (Common.fact 638).pointIds 638), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 640).pointIds 640), B0976]
theorem treeEq0975 : B0975.tree = HexagonCover.N7900.SplitData.node0975 := by
  change Tree.branch (99 : Fin 170) _ = Tree.branch (99 : Fin 170) _
  apply congrArg (Tree.branch (99 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0976

def B0974 : Block := .branch 166 ![590295810358705652097, 1538, 9295429630892709892, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 748294547304193117959810867494614704044382993383456, 21778071483257206425470398235358640209984] ![B0975, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq0974 : B0974.tree = HexagonCover.N7900.SplitData.node0974 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0975
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0973 : Block := .branch 169 ![10141204802416131022332331295105, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 5708990770823839524233143877797980545531379744, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 565).pointIds 565), B0974, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0973 : B0973.tree = HexagonCover.N7900.SplitData.node0973 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0974
  · rfl

def B0972 : Block := .branch 141 ![10141204802416131022332331295105, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), B0973, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0972 : B0972.tree = HexagonCover.N7900.SplitData.node0972 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0973
  · rfl
  · rfl

def B0971 : Block := .branch 144 ![10141204802416131022332331295105, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0972, (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0971 : B0971.tree = HexagonCover.N7900.SplitData.node0971 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0972
  · rfl

def B0889 : Block := .branch 86 ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 329).pointIds 329), (.leaf 1 (Common.fact 330).pointIds 330), (.leaf 2 (Common.fact 331).pointIds 331), Tip0889_0890, (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), B0971]
theorem treeEq0889 : B0889.tree = HexagonCover.N7900.SplitData.node0889 := by
  change Tree.branch (86 : Fin 170) _ = Tree.branch (86 : Fin 170) _
  apply congrArg (Tree.branch (86 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0971

theorem accepted0889 : B0889.accepted = true := by decide +kernel
theorem checked0889 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0889 (maskNeeds ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0889]
  exact B0889.sound accepted0889
#print axioms checked0889

def B1023 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1023 : B1023.tree = HexagonCover.N7900.SplitData.node1023 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1022 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1023]
theorem treeEq1022 : B1022.tree = HexagonCover.N7900.SplitData.node1022 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1023

def B1021 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1022, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1021 : B1021.tree = HexagonCover.N7900.SplitData.node1021 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1022
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1020 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1021, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1020 : B1020.tree = HexagonCover.N7900.SplitData.node1020 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1021
  · rfl
  · rfl

def B1019 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1020, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1019 : B1019.tree = HexagonCover.N7900.SplitData.node1019 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1020
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1018 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1019, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1018 : B1018.tree = HexagonCover.N7900.SplitData.node1018 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1019
  · rfl

def B1017 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1018, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1017 : B1017.tree = HexagonCover.N7900.SplitData.node1017 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1018
  · rfl
  · rfl

def B1016 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1017]
theorem treeEq1016 : B1016.tree = HexagonCover.N7900.SplitData.node1016 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1017

def B1025 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1025 : B1025.tree = HexagonCover.N7900.SplitData.node1025 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1024 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1025, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1024 : B1024.tree = HexagonCover.N7900.SplitData.node1024 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1025
  · rfl
  · rfl

def B1015 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1016, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1024]
theorem treeEq1015 : B1015.tree = HexagonCover.N7900.SplitData.node1015 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1016
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1024

def B1032 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1032 : B1032.tree = HexagonCover.N7900.SplitData.node1032 := by
  change Tree.branch (100 : Fin 170) _ = Tree.branch (100 : Fin 170) _
  apply congrArg (Tree.branch (100 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1031 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1032]
theorem treeEq1031 : B1031.tree = HexagonCover.N7900.SplitData.node1031 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1032

def B1030 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1031, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1030 : B1030.tree = HexagonCover.N7900.SplitData.node1030 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1029 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1030, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1029 : B1029.tree = HexagonCover.N7900.SplitData.node1029 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1030
  · rfl
  · rfl

def B1028 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1029, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1028 : B1028.tree = HexagonCover.N7900.SplitData.node1028 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1029
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1027 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1028, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1027 : B1027.tree = HexagonCover.N7900.SplitData.node1027 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1028
  · rfl

def B1026 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1027, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1026 : B1026.tree = HexagonCover.N7900.SplitData.node1026 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1027
  · rfl
  · rfl

def B1014 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1015, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1026]
theorem treeEq1014 : B1014.tree = HexagonCover.N7900.SplitData.node1014 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1015
  · rfl
  · rfl
  · rfl
  · exact treeEq1026

theorem accepted1014 : B1014.accepted = true := by decide +kernel
theorem checked1014 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1014 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1014]
  exact B1014.sound accepted1014
#print axioms checked1014

end HexagonCover.N7900.SplitAlignedTree.Run0012
