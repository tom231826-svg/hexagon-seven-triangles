import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0050 : Block := .branch 168 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 2923003361774091768167693683308920878111708438536, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M6667_6700.SplitData.node0050 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0049 : Block := .branch 167 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 2923003361774091768167693683308920878111708438536, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 248).pointIds 248), (.leaf 5 (Common.fact 249).pointIds 249), B0050]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M6667_6700.SplitData.node0049 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0050

def B0052 : Block := .branch 168 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 26398373324289433960054057290937862042535281655824, 1432833768041334006874500727005095043342401568, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 260).pointIds 260), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M6667_6700.SplitData.node0052 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0051 : Block := .branch 167 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 26398373324289433960054057290937862042535281655824, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 258).pointIds 258), (.leaf 5 (Common.fact 249).pointIds 249), B0052]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M6667_6700.SplitData.node0051 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0052

def B0053 : Block := .branch 168 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2923006067699473524104567300440190558166538780736] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 261).pointIds 261)]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M6667_6700.SplitData.node0053 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0048 : Block := .branch 161 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 240).pointIds 240), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), B0049, B0051, (.leaf 5 (Common.fact 243).pointIds 243), B0053]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M6667_6700.SplitData.node0048 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0049
  · exact treeEq0051
  · rfl
  · exact treeEq0053

def B0055 : Block := .branch 168 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 1461501724443188849963931479340182522188594700296, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 265).pointIds 265), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M6667_6700.SplitData.node0055 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0054 : Block := .branch 167 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 1461501724443188849963931479340182522188594700296, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 263).pointIds 263), (.leaf 4 (Common.fact 248).pointIds 248), (.leaf 5 (Common.fact 249).pointIds 249), B0055]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M6667_6700.SplitData.node0054 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0055

def B0056 : Block := .branch 167 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 1461504430368570606217640375276054216350419648576] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 248).pointIds 248), (.leaf 5 (Common.fact 249).pointIds 249), (.leaf 6 (Common.fact 266).pointIds 266)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M6667_6700.SplitData.node0056 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0047 : Block := .branch 160 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), B0048, B0054, (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B0056]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M6667_6700.SplitData.node0047 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0048
  · exact treeEq0054
  · rfl
  · rfl
  · exact treeEq0056

def B0058 : Block := .branch 168 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 730750818665451459101842418719324751262788884484, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 269).pointIds 269), (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M6667_6700.SplitData.node0058 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0057 : Block := .branch 167 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 730750818665451459101842418719324751262788884484, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 267).pointIds 267), (.leaf 2 (Common.fact 268).pointIds 268), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 248).pointIds 248), (.leaf 5 (Common.fact 249).pointIds 249), B0058]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M6667_6700.SplitData.node0057 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0058

def B0060 : Block := .branch 168 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 187802963184614174805818461088569120130290813501504] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 269).pointIds 269), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 254).pointIds 254), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 271).pointIds 271)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M6667_6700.SplitData.node0060 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0059 : Block := .branch 167 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 730753606258601275746802500884893614331448000576] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 267).pointIds 267), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 248).pointIds 248), (.leaf 5 (Common.fact 249).pointIds 249), B0060]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M6667_6700.SplitData.node0059 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0060

def B0046 : Block := .branch 159 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 232).pointIds 232), B0047, B0057, (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B0059]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M6667_6700.SplitData.node0046 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0047
  · exact treeEq0057
  · rfl
  · rfl
  · rfl
  · exact treeEq0059

def B0062 : Block := .branch 168 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 5937350401656793429721023291336626550508246630416, 23385459031062488025265831824187533409538263089184, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 269).pointIds 269), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 274).pointIds 274), (.leaf 5 (Common.fact 275).pointIds 275), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M6667_6700.SplitData.node0062 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0061 : Block := .branch 167 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 5937350401656793429721023291336626550508246630416, 23385459031062488025265831824187533409538263089184, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 267).pointIds 267), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), B0062]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M6667_6700.SplitData.node0061 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0062

def B0045 : Block := .branch 164 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 5937350401656793429721023291336626550508246630416, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), B0046, B0061, (.leaf 0 [] 0)]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M6667_6700.SplitData.node0045 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0046
  · exact treeEq0061
  · rfl

def B0063 : Block := .branch 168 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 5846009342361279360828849615929813947852579668032] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 269).pointIds 269), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 277).pointIds 277)]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M6667_6700.SplitData.node0063 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0044 : Block := .branch 162 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), B0045, (.leaf 5 (Common.fact 227).pointIds 227), B0063]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M6667_6700.SplitData.node0044 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0045
  · rfl
  · exact treeEq0063

theorem accepted0044 : B0044.accepted = true := by decide +kernel
theorem checked0044 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0044 (maskNeeds ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128]) := by
  rw [← treeEq0044]
  exact B0044.sound accepted0044
#print axioms checked0044

def Tip0038_0044 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0044 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] checked0044
def B0065 : Block := .branch 168 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 187437587775281449076267849365399870720445555146816] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 255).pointIds 255), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M6667_6700.SplitData.node0065 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0064 : Block := .branch 167 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 365378196925875546196190777715644204486189645888] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 279).pointIds 279), (.leaf 5 (Common.fact 249).pointIds 249), B0065]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M6667_6700.SplitData.node0064 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065

def B0043 : Block := .branch 158 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 218).pointIds 218), Tip0038_0044, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0064]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M6667_6700.SplitData.node0043 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0064

def B0067 : Block := .branch 168 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 91349438408516806513546516802323288635455438880, 187072212371393241218085768872748908385188214997056] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 284).pointIds 284), (.leaf 5 (Common.fact 285).pointIds 285), (.leaf 6 (Common.fact 256).pointIds 256)]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M6667_6700.SplitData.node0067 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0066 : Block := .branch 167 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 91349438408516806513546516802323288635455438880, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 282).pointIds 282), (.leaf 5 (Common.fact 283).pointIds 283), B0067]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M6667_6700.SplitData.node0066 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0067

def B0042 : Block := .branch 156 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 1432833768041334006874500727005095043342401568, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), B0043, B0066, (.leaf 0 [] 0)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M6667_6700.SplitData.node0042 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0043
  · exact treeEq0066
  · rfl

def B0069 : Block := .branch 168 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 5846720173169964977273822132276583609347942219792, 5586075335374125816214757555599906959654944, 1427253137223831567275879069347283320043995200] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 287).pointIds 287), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M6667_6700.SplitData.node0069 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0068 : Block := .branch 162 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 5586075335374125816214757555599906959654944, 1427253137223831567275879069347283320043995200] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), B0069, (.leaf 5 (Common.fact 227).pointIds 227), (.leaf 6 (Common.fact 286).pointIds 286)]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M6667_6700.SplitData.node0068 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0069
  · rfl
  · rfl

def B0041 : Block := .branch 150 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 5586075335374125816214757555599906959654944, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), B0042, B0068]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M6667_6700.SplitData.node0041 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0042
  · exact treeEq0068

def B0071 : Block := .branch 167 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 1432833768041334006874500727005095043342401568, 716416884020667954639428049406616797040869440] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 291).pointIds 291), (.leaf 5 (Common.fact 249).pointIds 249), (.leaf 6 (Common.fact 292).pointIds 292)]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M6667_6700.SplitData.node0071 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0070 : Block := .branch 150 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 5586075335374125816214757555599906959654944, 716416884020667954639428049406616797040869440] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), B0071, (.leaf 6 (Common.fact 290).pointIds 290)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M6667_6700.SplitData.node0070 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0071
  · rfl

def B0040 : Block := .branch 149 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 5586075335374125816214757555599906959654944, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B0041, (.leaf 5 (Common.fact 208).pointIds 208), B0070]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M6667_6700.SplitData.node0040 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0041
  · rfl
  · exact treeEq0070

def B0073 : Block := .branch 168 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 10889035741470030830827987437816583159840, 8362779449449934880253580256312410934607936] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 259).pointIds 259), (.leaf 4 (Common.fact 284).pointIds 284), (.leaf 5 (Common.fact 294).pointIds 294), (.leaf 6 (Common.fact 295).pointIds 295)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M6667_6700.SplitData.node0073 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0072 : Block := .branch 149 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 324518553658426726783156020674576, 10889035741470030830827987437816583159840, 8362779449449934880253580256312410934607936] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B0073, (.leaf 5 (Common.fact 208).pointIds 208), (.leaf 6 (Common.fact 293).pointIds 293)]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M6667_6700.SplitData.node0072 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0073
  · rfl
  · rfl

def B0039 : Block := .branch 142 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), B0040, B0072]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M6667_6700.SplitData.node0039 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0040
  · exact treeEq0072

def B0075 : Block := .branch 167 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1361129792202307512280225212883093520400, 1427258581741701351089116797436932952965906464, 4186834242596178056631047073909751443619904] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 297).pointIds 297), (.leaf 5 (Common.fact 298).pointIds 298), (.leaf 6 (Common.fact 299).pointIds 299)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M6667_6700.SplitData.node0075 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0074 : Block := .branch 150 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 4186834242596178056631047073909751443619904] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), B0075, (.leaf 6 (Common.fact 296).pointIds 296)]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M6667_6700.SplitData.node0074 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0075
  · rfl

def B0038 : Block := .branch 140 ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0039, (.leaf 5 (Common.fact 198).pointIds 198), B0074]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M6667_6700.SplitData.node0038 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0039
  · rfl
  · exact treeEq0074

theorem accepted0038 : B0038.accepted = true := by decide +kernel
theorem checked0038 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0038 (maskNeeds ![53171715979825902331119469163985240449, 618970019642691236961191426, 77919046967349146032132, 87112285931760324017876354838799843352584, 1361129792202307512280225212883093520400, 10889035741470030830827987437816583159840, 2793037667688014110285064681869228849496128]) := by
  rw [← treeEq0038]
  exact B0038.sound accepted0038
#print axioms checked0038

def B0096 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 2923003361774091768167693683308920878111708438536, 29321376598951240120979980614797154865003167318032, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 329).pointIds 329), (.leaf 3 (Common.fact 330).pointIds 330), (.leaf 4 (Common.fact 331).pointIds 331), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M6667_6700.SplitData.node0096 := by
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

def B0097 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 26398373324289433960054057290937862042535281655824, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 329).pointIds 329), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M6667_6700.SplitData.node0097 := by
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

def B0098 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 2787593149816327892691964784081045188640800, 377067422444984247573388534864345824714119804616768] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 329).pointIds 329), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 331).pointIds 331), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 336).pointIds 336)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M6667_6700.SplitData.node0098 := by
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

def B0095 : Block := .branch 161 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 1461501637330902918203684910635329987005078575108, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 240).pointIds 240), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), B0096, B0097, (.leaf 5 (Common.fact 243).pointIds 243), B0098]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M6667_6700.SplitData.node0095 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0096
  · exact treeEq0097
  · rfl
  · exact treeEq0098

def B0099 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 1461501724443188849963931479340182522188594700296, 29321376598951240120979980614797154865003167318032, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 331).pointIds 331), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M6667_6700.SplitData.node0099 := by
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

def B0100 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 2787593149816327892691964784081045188640800, 1461501650942197595358445506318146012919316873280] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 331).pointIds 331), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 339).pointIds 339)]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M6667_6700.SplitData.node0100 := by
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

def B0094 : Block := .branch 160 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 29321376598951240120979980614797154865003167318032, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), B0095, B0099, (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B0100]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M6667_6700.SplitData.node0094 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0095
  · exact treeEq0099
  · rfl
  · rfl
  · exact treeEq0100

def B0101 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 5937350401656793429721023291336626550508246630416, 23384028984887596507586850015425312395540109328416, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 340).pointIds 340), (.leaf 5 (Common.fact 341).pointIds 341), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M6667_6700.SplitData.node0101 := by
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

def B0093 : Block := .branch 164 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 5937350401656793429721023291336626550508246630416, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), B0094, B0101, (.leaf 0 [] 0)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M6667_6700.SplitData.node0093 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0094
  · exact treeEq0101
  · rfl

def B0102 : Block := .branch 169 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 2787593149816327892691964784081045188640800, 379990425719646053410112817179835448103805845504064] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 328).pointIds 328), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 342).pointIds 342), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M6667_6700.SplitData.node0102 := by
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

def B0092 : Block := .branch 162 ![53171715979825902331119469163985240449, 1096126227998177188652763624537212265841461036546, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), B0093, (.leaf 5 (Common.fact 227).pointIds 227), B0102]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M6667_6700.SplitData.node0092 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0093
  · rfl
  · exact treeEq0102

def B0103 : Block := .branch 169 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 730750818665451459101842418719324751262788884484, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 344).pointIds 344), (.leaf 2 (Common.fact 345).pointIds 345), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 342).pointIds 342), (.leaf 5 (Common.fact 332).pointIds 332), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M6667_6700.SplitData.node0103 := by
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

def B0091 : Block := .branch 159 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 91343852333181756906283960471494471884516458512, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 232).pointIds 232), B0092, B0103, (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), (.leaf 6 (Common.fact 326).pointIds 326)]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M6667_6700.SplitData.node0091 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0092
  · exact treeEq0103
  · rfl
  · rfl
  · rfl
  · rfl

def B0104 : Block := .branch 169 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 91346639926331248715622994009551769773684424736, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 344).pointIds 344), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 346).pointIds 346), (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M6667_6700.SplitData.node0104 := by
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

def B0090 : Block := .branch 156 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 713623846353304459082801411451530724212047888, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), B0091, B0104, (.leaf 0 [] 0)]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M6667_6700.SplitData.node0090 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0091
  · exact treeEq0104
  · rfl

def B0105 : Block := .branch 169 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 716411439502796268421834949508828613380014112, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 344).pointIds 344), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 348).pointIds 348), (.leaf 5 (Common.fact 349).pointIds 349), (.leaf 6 (Common.fact 333).pointIds 333)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M6667_6700.SplitData.node0105 := by
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

def B0089 : Block := .branch 149 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 2787593149816327892691964784081045188640800, 374144419170322441737298232591475226697716477722688] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B0090, B0105, (.leaf 6 (Common.fact 325).pointIds 325)]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M6667_6700.SplitData.node0089 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0090
  · exact treeEq0105
  · rfl

theorem accepted0089 : B0089.accepted = true := by decide +kernel
theorem checked0089 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0089 (maskNeeds ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 2787593149816327892691964784081045188640800, 374144419170322441737298232591475226697716477722688]) := by
  rw [← treeEq0089]
  exact B0089.sound accepted0089
#print axioms checked0089

def Tip0082_0089 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0089 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 87112285931760324017876354838799843352584, 1393796575232682500004409118823678614798352, 2787593149816327892691964784081045188640800, 374144419170322441737298232591475226697716477722688] checked0089
def B0109 : Block := .branch 169 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 1480908861164442746651033018326211276931088, 116920133774065383272622679309267425653519792078880, 379990425719646053410112817179835448103805845504064] ![(.leaf 0 (Common.fact 327).pointIds 327), (.leaf 1 (Common.fact 344).pointIds 344), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M6667_6700.SplitData.node0109 := by
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

def B0108 : Block := .branch 162 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 1480908861164442746651033018326211276931088, 116920133774065383272622679309267425653519792078880, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 352).pointIds 352), (.leaf 5 (Common.fact 227).pointIds 227), B0109]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M6667_6700.SplitData.node0108 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0109

def B0107 : Block := .branch 164 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 1480908861164442746651033018326211276931088, 93536107576770936581363721985806897339024871391264, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 351).pointIds 351), B0108, (.leaf 0 [] 0)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M6667_6700.SplitData.node0107 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0108
  · rfl

def B0106 : Block := .branch 166 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 1480908861164442746651033018326211276931088, 2787593149816327892691964784081045188640800, 374144419170322441737298077848970316025182115332160] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 350).pointIds 350), B0107, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M6667_6700.SplitData.node0106 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0107
  · rfl

def B0088 : Block := .branch 136 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 1393796575232682500004409118823678614798352, 2787593149816327892691964784081045188640800, 374144419170322441737298232591475226697716477722688] ![(.leaf 0 (Common.fact 190).pointIds 190), (.leaf 1 (Common.fact 191).pointIds 191), (.leaf 2 (Common.fact 192).pointIds 192), Tip0082_0089, B0106, (.leaf 5 (Common.fact 193).pointIds 193), (.leaf 0 [] 0)]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M6667_6700.SplitData.node0088 := by
  change Tree.branch (136 : Fin 173) _ = Tree.branch (136 : Fin 173) _
  apply congrArg (Tree.branch (136 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0106
  · rfl
  · rfl

def B0087 : Block := .branch 140 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 2787593149816327892691964784081045188640800, 374144419170322441737298232591475226697716477722688] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0088, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M6667_6700.SplitData.node0087 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · rfl
  · rfl

def B0086 : Block := .branch 141 ![53171715979825902331119469163985240449, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419170322441737298232591475226697716477722688] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), B0087, (.leaf 6 (Common.fact 323).pointIds 323)]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M6667_6700.SplitData.node0086 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0087
  · rfl

def B0085 : Block := .branch 158 ![53171715979825902331119469163985240449, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 393248, 374144419170322441737298232591475226697716477722688] ![(.leaf 0 (Common.fact 218).pointIds 218), B0086, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 322).pointIds 322)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M6667_6700.SplitData.node0085 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0086
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 125 ![10636420114708594398197643235014214017, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 324518553658426726783156020674576, 187072209578355573530071658587684226515959365894176, 374144419170322441737298232591475226697716477722688] ![B0085, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 321).pointIds 321)]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M6667_6700.SplitData.node0084 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0085
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0083 : Block := .branch 167 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 393248, 374144419170322441737298232591475226697716477722688] ![(.leaf 0 (Common.fact 313).pointIds 313), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 297).pointIds 297), B0084, (.leaf 6 (Common.fact 319).pointIds 319)]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M6667_6700.SplitData.node0083 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0084
  · rfl

def B0082 : Block := .branch 168 ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 393248, 13611294677154915416106773665797746720832] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 310).pointIds 310), (.leaf 4 (Common.fact 316).pointIds 316), (.leaf 5 (Common.fact 318).pointIds 318), B0083]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M6667_6700.SplitData.node0082 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0083

theorem accepted0082 : B0082.accepted = true := by decide +kernel
theorem checked0082 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0082 (maskNeeds ![10636420114708594398197643235014214017, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1361129792202307512280225212883093520400, 393248, 13611294677154915416106773665797746720832]) := by
  rw [← treeEq0082]
  exact B0082.sound accepted0082
#print axioms checked0082

end HexagonCover.NBand.M6667_6700.SplitTree.Run0000
