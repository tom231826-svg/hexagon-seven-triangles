import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0028
import HexagonCover.NBand.M8500_8700.SplitTree.Run0029
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0030
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1923_1927 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1927 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0028.checked1927
def Tip1923_2056 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2056 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0029.checked2056
def B2054 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2054 : B2054.tree = HexagonCover.NBand.M8500_8700.SplitData.node2054 := by
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
  · rfl

def B2053 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2054, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq2053 : B2053.tree = HexagonCover.NBand.M8500_8700.SplitData.node2053 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2054
  · rfl
  · rfl
  · rfl

def B2052 : Block := .branch 160 ![1237940039864092827016233345, 928606145227516381595960834, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2053]
theorem treeEq2052 : B2052.tree = HexagonCover.NBand.M8500_8700.SplitData.node2052 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2053

def B1926 : Block := .branch 89 ![1237940039864092827016233345, 309636125584826244146398722, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![Tip1923_1927, B2052, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq1926 : B1926.tree = HexagonCover.NBand.M8500_8700.SplitData.node1926 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2052
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2183 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2183 : B2183.tree = HexagonCover.NBand.M8500_8700.SplitData.node2183 := by
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
  · rfl

def B2182 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2183, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq2182 : B2182.tree = HexagonCover.NBand.M8500_8700.SplitData.node2182 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2183
  · rfl
  · rfl
  · rfl

def B2181 : Block := .branch 160 ![1237940039864092827016233345, 619196693269897227194598914, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2182]
theorem treeEq2181 : B2181.tree = HexagonCover.NBand.M8500_8700.SplitData.node2181 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2182

def B2055 : Block := .branch 89 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![Tip1923_2056, B2181, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq2055 : B2055.tree = HexagonCover.NBand.M8500_8700.SplitData.node2055 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2181
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1925 : Block := .branch 88 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), B1926, B2055, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq1925 : B1925.tree = HexagonCover.NBand.M8500_8700.SplitData.node1925 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1926
  · exact treeEq2055
  · rfl
  · rfl
  · rfl
  · rfl

def B2186 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq2186 : B2186.tree = HexagonCover.NBand.M8500_8700.SplitData.node2186 := by
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

def B2185 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2186, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2185 : B2185.tree = HexagonCover.NBand.M8500_8700.SplitData.node2185 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2186
  · rfl

def B2184 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2185]
theorem treeEq2184 : B2184.tree = HexagonCover.NBand.M8500_8700.SplitData.node2184 := by
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
  · exact treeEq2185

def B1924 : Block := .branch 86 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B1925, B2184, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq1924 : B1924.tree = HexagonCover.NBand.M8500_8700.SplitData.node1924 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1925
  · exact treeEq2184
  · rfl
  · rfl
  · rfl

def B2189 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq2189 : B2189.tree = HexagonCover.NBand.M8500_8700.SplitData.node2189 := by
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

def B2188 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2189, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2188 : B2188.tree = HexagonCover.NBand.M8500_8700.SplitData.node2188 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2189
  · rfl

def B2187 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2188]
theorem treeEq2187 : B2187.tree = HexagonCover.NBand.M8500_8700.SplitData.node2187 := by
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
  · exact treeEq2188

def B1923 : Block := .branch 85 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B1924, B2187, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq1923 : B1923.tree = HexagonCover.NBand.M8500_8700.SplitData.node1923 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1924
  · exact treeEq2187
  · rfl
  · rfl
  · rfl

theorem accepted1923 : B1923.accepted = true := by decide +kernel
theorem checked1923 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1923 (maskNeeds ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1923]
  exact B1923.sound accepted1923
#print axioms checked1923

def B2230 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2230 : B2230.tree = HexagonCover.NBand.M8500_8700.SplitData.node2230 := by
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

def B2229 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2230, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq2229 : B2229.tree = HexagonCover.NBand.M8500_8700.SplitData.node2229 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2230
  · rfl

def B2228 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2229]
theorem treeEq2228 : B2228.tree = HexagonCover.NBand.M8500_8700.SplitData.node2228 := by
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
  · exact treeEq2229

def B2227 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2228, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq2227 : B2227.tree = HexagonCover.NBand.M8500_8700.SplitData.node2227 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2228
  · rfl
  · rfl
  · rfl

def B2226 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B2227]
theorem treeEq2226 : B2226.tree = HexagonCover.NBand.M8500_8700.SplitData.node2226 := by
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
  · exact treeEq2227

def B2232 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq2232 : B2232.tree = HexagonCover.NBand.M8500_8700.SplitData.node2232 := by
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
  · rfl

def B2231 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2232, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq2231 : B2231.tree = HexagonCover.NBand.M8500_8700.SplitData.node2231 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2232
  · rfl
  · rfl
  · rfl

def B2225 : Block := .branch 144 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B2226, B2231]
theorem treeEq2225 : B2225.tree = HexagonCover.NBand.M8500_8700.SplitData.node2225 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2226
  · exact treeEq2231

def B2238 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2238 : B2238.tree = HexagonCover.NBand.M8500_8700.SplitData.node2238 := by
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

def B2237 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2238, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq2237 : B2237.tree = HexagonCover.NBand.M8500_8700.SplitData.node2237 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2238
  · rfl

def B2236 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2237]
theorem treeEq2236 : B2236.tree = HexagonCover.NBand.M8500_8700.SplitData.node2236 := by
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
  · exact treeEq2237

def B2235 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2236, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq2235 : B2235.tree = HexagonCover.NBand.M8500_8700.SplitData.node2235 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2236
  · rfl
  · rfl
  · rfl

def B2234 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2235]
theorem treeEq2234 : B2234.tree = HexagonCover.NBand.M8500_8700.SplitData.node2234 := by
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
  · exact treeEq2235

def B2233 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2234, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq2233 : B2233.tree = HexagonCover.NBand.M8500_8700.SplitData.node2233 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2234
  · rfl

def B2224 : Block := .branch 142 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B2225, (.leaf 5 (Common.fact 339).pointIds 339), B2233]
theorem treeEq2224 : B2224.tree = HexagonCover.NBand.M8500_8700.SplitData.node2224 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2225
  · rfl
  · exact treeEq2233

theorem accepted2224 : B2224.accepted = true := by decide +kernel
theorem checked2224 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2224 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq2224]
  exact B2224.sound accepted2224
#print axioms checked2224

def Tip2221_2224 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2224 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked2224
def B2243 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2243 : B2243.tree = HexagonCover.NBand.M8500_8700.SplitData.node2243 := by
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

def B2242 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2243, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2242 : B2242.tree = HexagonCover.NBand.M8500_8700.SplitData.node2242 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2243
  · rfl

def B2241 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B2242]
theorem treeEq2241 : B2241.tree = HexagonCover.NBand.M8500_8700.SplitData.node2241 := by
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
  · exact treeEq2242

def B2240 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B2241, (.leaf 0 [] 0)]
theorem treeEq2240 : B2240.tree = HexagonCover.NBand.M8500_8700.SplitData.node2240 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2241
  · rfl

def B2239 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B2240, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2239 : B2239.tree = HexagonCover.NBand.M8500_8700.SplitData.node2239 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2240
  · rfl

def B2223 : Block := .branch 138 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip2221_2224, B2239, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq2223 : B2223.tree = HexagonCover.NBand.M8500_8700.SplitData.node2223 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2239
  · rfl
  · rfl

def B2249 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq2249 : B2249.tree = HexagonCover.NBand.M8500_8700.SplitData.node2249 := by
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

def B2248 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2249, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq2248 : B2248.tree = HexagonCover.NBand.M8500_8700.SplitData.node2248 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2249
  · rfl

def B2247 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2248]
theorem treeEq2247 : B2247.tree = HexagonCover.NBand.M8500_8700.SplitData.node2247 := by
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
  · exact treeEq2248

def B2246 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2247, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq2246 : B2246.tree = HexagonCover.NBand.M8500_8700.SplitData.node2246 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2247
  · rfl
  · rfl
  · rfl

def B2245 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2246]
theorem treeEq2245 : B2245.tree = HexagonCover.NBand.M8500_8700.SplitData.node2245 := by
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
  · exact treeEq2246

def B2244 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2245, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq2244 : B2244.tree = HexagonCover.NBand.M8500_8700.SplitData.node2244 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2245
  · rfl

def B2222 : Block := .branch 132 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B2223, (.leaf 5 (Common.fact 329).pointIds 329), B2244]
theorem treeEq2222 : B2222.tree = HexagonCover.NBand.M8500_8700.SplitData.node2222 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2223
  · rfl
  · exact treeEq2244

def B2254 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq2254 : B2254.tree = HexagonCover.NBand.M8500_8700.SplitData.node2254 := by
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

def B2253 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2254, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq2253 : B2253.tree = HexagonCover.NBand.M8500_8700.SplitData.node2253 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2254
  · rfl

def B2252 : Block := .branch 163 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B2253]
theorem treeEq2252 : B2252.tree = HexagonCover.NBand.M8500_8700.SplitData.node2252 := by
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
  · exact treeEq2253

def B2251 : Block := .branch 165 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B2252, (.leaf 0 [] 0)]
theorem treeEq2251 : B2251.tree = HexagonCover.NBand.M8500_8700.SplitData.node2251 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2252
  · rfl

def B2250 : Block := .branch 167 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B2251, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq2250 : B2250.tree = HexagonCover.NBand.M8500_8700.SplitData.node2250 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2251
  · rfl

def B2221 : Block := .branch 129 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B2222, B2250, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq2221 : B2221.tree = HexagonCover.NBand.M8500_8700.SplitData.node2221 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2222
  · exact treeEq2250
  · rfl
  · rfl

theorem accepted2221 : B2221.accepted = true := by decide +kernel
theorem checked2221 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2221 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq2221]
  exact B2221.sound accepted2221
#print axioms checked2221

def B2283 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2283 : B2283.tree = HexagonCover.NBand.M8500_8700.SplitData.node2283 := by
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

def B2282 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2283, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq2282 : B2282.tree = HexagonCover.NBand.M8500_8700.SplitData.node2282 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2283
  · rfl

def B2281 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2282]
theorem treeEq2281 : B2281.tree = HexagonCover.NBand.M8500_8700.SplitData.node2281 := by
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
  · exact treeEq2282

def B2280 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2281, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq2280 : B2280.tree = HexagonCover.NBand.M8500_8700.SplitData.node2280 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2281
  · rfl
  · rfl
  · rfl

def B2279 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B2280]
theorem treeEq2279 : B2279.tree = HexagonCover.NBand.M8500_8700.SplitData.node2279 := by
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
  · exact treeEq2280

def B2285 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq2285 : B2285.tree = HexagonCover.NBand.M8500_8700.SplitData.node2285 := by
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
  · rfl

def B2284 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160338284096688146337959329517314506816] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2285, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq2284 : B2284.tree = HexagonCover.NBand.M8500_8700.SplitData.node2284 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2285
  · rfl
  · rfl
  · rfl

def B2278 : Block := .branch 144 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B2279, B2284]
theorem treeEq2278 : B2278.tree = HexagonCover.NBand.M8500_8700.SplitData.node2278 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2279
  · exact treeEq2284

def B2291 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2291 : B2291.tree = HexagonCover.NBand.M8500_8700.SplitData.node2291 := by
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

def B2290 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2291, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq2290 : B2290.tree = HexagonCover.NBand.M8500_8700.SplitData.node2290 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2291
  · rfl

def B2289 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2290]
theorem treeEq2289 : B2289.tree = HexagonCover.NBand.M8500_8700.SplitData.node2289 := by
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
  · exact treeEq2290

def B2288 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2289, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq2288 : B2288.tree = HexagonCover.NBand.M8500_8700.SplitData.node2288 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2289
  · rfl
  · rfl
  · rfl

def B2287 : Block := .branch 168 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 915).pointIds 915), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B2288]
theorem treeEq2287 : B2287.tree = HexagonCover.NBand.M8500_8700.SplitData.node2287 := by
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
  · exact treeEq2288

def B2286 : Block := .branch 152 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157582352009455317861204594512516087872] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B2287, (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq2286 : B2286.tree = HexagonCover.NBand.M8500_8700.SplitData.node2286 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2287
  · rfl

def B2277 : Block := .branch 142 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B2278, (.leaf 5 (Common.fact 339).pointIds 339), B2286]
theorem treeEq2277 : B2277.tree = HexagonCover.NBand.M8500_8700.SplitData.node2277 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2278
  · rfl
  · exact treeEq2286

theorem accepted2277 : B2277.accepted = true := by decide +kernel
theorem checked2277 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2277 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971282719353669933931636432422139592768]) := by
  rw [← treeEq2277]
  exact B2277.sound accepted2277
#print axioms checked2277

end HexagonCover.NBand.M8500_8700.SplitTree.Run0030
