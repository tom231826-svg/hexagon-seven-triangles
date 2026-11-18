import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0028
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0029
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0028_0030 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0030 ![578712552117109121, 151152765055713897612802, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0028.checked0030
def B2103 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 11150372599265311570767859136324180753088528, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 727).pointIds 727), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq2103 : B2103.tree = HexagonCover.NBand.M8300_8500.SplitData.node2103 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2102 : Block := .branch 143 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B2103, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq2102 : B2102.tree = HexagonCover.NBand.M8300_8500.SplitData.node2102 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2103
  · rfl
  · rfl

def B2101 : Block := .branch 144 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B2102, (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq2101 : B2101.tree = HexagonCover.NBand.M8300_8500.SplitData.node2101 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2102
  · rfl

def B2100 : Block := .branch 107 ![385, 1538, 6148, 81129638414606681695789005168648, 3032901347000164747248857685080177164813434896, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2101, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2100 : B2100.tree = HexagonCover.NBand.M8300_8500.SplitData.node2100 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2101
  · rfl
  · rfl
  · rfl

def B2099 : Block := .branch 118 ![385, 1538, 6148, 81129638414606681695789005168648, 3032901347000164747248857685080177164813434896, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B2100, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2099 : B2099.tree = HexagonCover.NBand.M8300_8500.SplitData.node2099 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2100
  · rfl
  · rfl
  · rfl

def B2098 : Block := .branch 128 ![385, 1538, 6148, 81129638414606681695789005168648, 3032901347000164747248857685080177164813434896, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2099, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2098 : B2098.tree = HexagonCover.NBand.M8300_8500.SplitData.node2098 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2099
  · rfl
  · rfl
  · rfl

def B2097 : Block := .branch 151 ![385, 1538, 6148, 81129638414606681695789005168648, 178405961588244985132285746181186892047941648, 393248, 21804656042855760130229778469217174552640] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B2098, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq2097 : B2097.tree = HexagonCover.NBand.M8300_8500.SplitData.node2097 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2098
  · rfl
  · rfl

def B0029 : Block := .branch 77 ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 163).pointIds 163), Tip0028_0030, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B2097]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M8300_8500.SplitData.node0029 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2097

def B2110 : Block := .branch 120 ![385, 1538, 6148, 24584, 11150372599265311570767859136324180753088528, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq2110 : B2110.tree = HexagonCover.NBand.M8300_8500.SplitData.node2110 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2109 : Block := .branch 143 ![385, 1538, 6148, 24584, 98320, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B2110, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 932).pointIds 932)]
theorem treeEq2109 : B2109.tree = HexagonCover.NBand.M8300_8500.SplitData.node2109 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2110
  · rfl
  · rfl

def B2108 : Block := .branch 144 ![385, 1538, 6148, 24584, 98320, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B2109, (.leaf 6 (Common.fact 931).pointIds 931)]
theorem treeEq2108 : B2108.tree = HexagonCover.NBand.M8300_8500.SplitData.node2108 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2109
  · rfl

def B2107 : Block := .branch 107 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2108, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2107 : B2107.tree = HexagonCover.NBand.M8300_8500.SplitData.node2107 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2108
  · rfl
  · rfl
  · rfl

def B2106 : Block := .branch 118 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B2107, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2106 : B2106.tree = HexagonCover.NBand.M8300_8500.SplitData.node2106 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2107
  · rfl
  · rfl
  · rfl

def B2105 : Block := .branch 128 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2106, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2105 : B2105.tree = HexagonCover.NBand.M8300_8500.SplitData.node2105 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2106
  · rfl
  · rfl
  · rfl

def B2104 : Block := .branch 151 ![385, 1538, 6148, 24584, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979704346827747233366080] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B2105, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq2104 : B2104.tree = HexagonCover.NBand.M8300_8500.SplitData.node2104 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2105
  · rfl
  · rfl

def B0028 : Block := .branch 69 ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![B0029, (.leaf 1 (Common.fact 158).pointIds 158), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B2104]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M8300_8500.SplitData.node0028 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0029
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2104

theorem accepted0028 : B0028.accepted = true := by decide +kernel
theorem checked0028 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0028 (maskNeeds ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0028]
  exact B0028.sound accepted0028
#print axioms checked0028

def B2158 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq2158 : B2158.tree = HexagonCover.NBand.M8300_8500.SplitData.node2158 := by
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

def B2157 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2158, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq2157 : B2157.tree = HexagonCover.NBand.M8300_8500.SplitData.node2157 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2158
  · rfl
  · rfl
  · rfl

def B2156 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42535295865117307932921825928971419680, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B2157]
theorem treeEq2156 : B2156.tree = HexagonCover.NBand.M8300_8500.SplitData.node2156 := by
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
  · exact treeEq2157

def B2162 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556142965880123323311949751266331459616, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq2162 : B2162.tree = HexagonCover.NBand.M8300_8500.SplitData.node2162 := by
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

def B2161 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2162, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq2161 : B2161.tree = HexagonCover.NBand.M8300_8500.SplitData.node2161 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2162
  · rfl

def B2160 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2161]
theorem treeEq2160 : B2160.tree = HexagonCover.NBand.M8300_8500.SplitData.node2160 := by
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
  · exact treeEq2161

def B2159 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2160, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2159 : B2159.tree = HexagonCover.NBand.M8300_8500.SplitData.node2159 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2160
  · rfl
  · rfl
  · rfl

def B2155 : Block := .branch 125 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B2156, B2159]
theorem treeEq2155 : B2155.tree = HexagonCover.NBand.M8300_8500.SplitData.node2155 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2156
  · exact treeEq2159

def B2166 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2166 : B2166.tree = HexagonCover.NBand.M8300_8500.SplitData.node2166 := by
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

def B2165 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2166, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2165 : B2165.tree = HexagonCover.NBand.M8300_8500.SplitData.node2165 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2166
  · rfl
  · rfl
  · rfl

def B2164 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422294120286634350736906063837462396960, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B2165]
theorem treeEq2164 : B2164.tree = HexagonCover.NBand.M8300_8500.SplitData.node2164 := by
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
  · exact treeEq2165

def B2163 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2164, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq2163 : B2163.tree = HexagonCover.NBand.M8300_8500.SplitData.node2163 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2164
  · rfl

def B2154 : Block := .branch 121 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B2155, (.leaf 5 (Common.fact 256).pointIds 256), B2163]
theorem treeEq2154 : B2154.tree = HexagonCover.NBand.M8300_8500.SplitData.node2154 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2155
  · rfl
  · exact treeEq2163

def B2171 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2171 : B2171.tree = HexagonCover.NBand.M8300_8500.SplitData.node2171 := by
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

def B2170 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2171, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2170 : B2170.tree = HexagonCover.NBand.M8300_8500.SplitData.node2170 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2171
  · rfl

def B2169 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B2170]
theorem treeEq2169 : B2169.tree = HexagonCover.NBand.M8300_8500.SplitData.node2169 := by
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
  · exact treeEq2170

def B2168 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B2169, (.leaf 0 [] 0)]
theorem treeEq2168 : B2168.tree = HexagonCover.NBand.M8300_8500.SplitData.node2168 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2169
  · rfl

def B2167 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B2168, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2167 : B2167.tree = HexagonCover.NBand.M8300_8500.SplitData.node2167 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2168
  · rfl

def B2153 : Block := .branch 119 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B2154, B2167, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2153 : B2153.tree = HexagonCover.NBand.M8300_8500.SplitData.node2153 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2154
  · exact treeEq2167
  · rfl
  · rfl

theorem accepted2153 : B2153.accepted = true := by decide +kernel
theorem checked2153 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2153 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2153]
  exact B2153.sound accepted2153
#print axioms checked2153

def Tip2152_2153 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2153 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked2153
def B2177 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq2177 : B2177.tree = HexagonCover.NBand.M8300_8500.SplitData.node2177 := by
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

def B2176 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2177, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq2176 : B2176.tree = HexagonCover.NBand.M8300_8500.SplitData.node2176 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2177
  · rfl
  · rfl
  · rfl

def B2175 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B2176]
theorem treeEq2175 : B2175.tree = HexagonCover.NBand.M8300_8500.SplitData.node2175 := by
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
  · exact treeEq2176

def B2181 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq2181 : B2181.tree = HexagonCover.NBand.M8300_8500.SplitData.node2181 := by
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

def B2180 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2181, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq2180 : B2180.tree = HexagonCover.NBand.M8300_8500.SplitData.node2180 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2181
  · rfl

def B2179 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2180]
theorem treeEq2179 : B2179.tree = HexagonCover.NBand.M8300_8500.SplitData.node2179 := by
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
  · exact treeEq2180

def B2178 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2179, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2178 : B2178.tree = HexagonCover.NBand.M8300_8500.SplitData.node2178 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2179
  · rfl
  · rfl
  · rfl

def B2174 : Block := .branch 125 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B2175, B2178]
theorem treeEq2174 : B2174.tree = HexagonCover.NBand.M8300_8500.SplitData.node2174 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2175
  · exact treeEq2178

def B2185 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2185 : B2185.tree = HexagonCover.NBand.M8300_8500.SplitData.node2185 := by
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

def B2184 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2185, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2184 : B2184.tree = HexagonCover.NBand.M8300_8500.SplitData.node2184 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2185
  · rfl
  · rfl
  · rfl

def B2183 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B2184]
theorem treeEq2183 : B2183.tree = HexagonCover.NBand.M8300_8500.SplitData.node2183 := by
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
  · exact treeEq2184

def B2182 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2183, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq2182 : B2182.tree = HexagonCover.NBand.M8300_8500.SplitData.node2182 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2183
  · rfl

def B2173 : Block := .branch 121 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B2174, (.leaf 5 (Common.fact 256).pointIds 256), B2182]
theorem treeEq2173 : B2173.tree = HexagonCover.NBand.M8300_8500.SplitData.node2173 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2174
  · rfl
  · exact treeEq2182

def B2190 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2190 : B2190.tree = HexagonCover.NBand.M8300_8500.SplitData.node2190 := by
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

def B2189 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2190, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2189 : B2189.tree = HexagonCover.NBand.M8300_8500.SplitData.node2189 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2190
  · rfl

def B2188 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B2189]
theorem treeEq2188 : B2188.tree = HexagonCover.NBand.M8300_8500.SplitData.node2188 := by
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
  · exact treeEq2189

def B2187 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B2188, (.leaf 0 [] 0)]
theorem treeEq2187 : B2187.tree = HexagonCover.NBand.M8300_8500.SplitData.node2187 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2188
  · rfl

def B2186 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B2187, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2186 : B2186.tree = HexagonCover.NBand.M8300_8500.SplitData.node2186 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2187
  · rfl

def B2172 : Block := .branch 119 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B2173, B2186, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2172 : B2172.tree = HexagonCover.NBand.M8300_8500.SplitData.node2172 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2173
  · exact treeEq2186
  · rfl
  · rfl

def B2152 : Block := .branch 115 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip2152_2153, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B2172, (.leaf 0 [] 0)]
theorem treeEq2152 : B2152.tree = HexagonCover.NBand.M8300_8500.SplitData.node2152 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2172
  · rfl

theorem accepted2152 : B2152.accepted = true := by decide +kernel
theorem checked2152 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2152 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2152]
  exact B2152.sound accepted2152
#print axioms checked2152

def Tip2149_2152 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2152 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked2152
def B2194 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq2194 : B2194.tree = HexagonCover.NBand.M8300_8500.SplitData.node2194 := by
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

def B2193 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2194, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2193 : B2193.tree = HexagonCover.NBand.M8300_8500.SplitData.node2193 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2194
  · rfl
  · rfl
  · rfl

def B2192 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400333925883571647971334348810992746560] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B2193]
theorem treeEq2192 : B2192.tree = HexagonCover.NBand.M8300_8500.SplitData.node2192 := by
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
  · exact treeEq2193

def B2191 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772933191195142415830470672991745736768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2192, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq2191 : B2191.tree = HexagonCover.NBand.M8300_8500.SplitData.node2191 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2192
  · rfl

def B2151 : Block := .branch 113 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip2149_2152, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B2191]
theorem treeEq2151 : B2151.tree = HexagonCover.NBand.M8300_8500.SplitData.node2151 := by
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
  · exact treeEq2191

def B2199 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2199 : B2199.tree = HexagonCover.NBand.M8300_8500.SplitData.node2199 := by
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

def B2198 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2199, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2198 : B2198.tree = HexagonCover.NBand.M8300_8500.SplitData.node2198 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2199
  · rfl

def B2197 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B2198]
theorem treeEq2197 : B2197.tree = HexagonCover.NBand.M8300_8500.SplitData.node2197 := by
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
  · exact treeEq2198

def B2196 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B2197, (.leaf 0 [] 0)]
theorem treeEq2196 : B2196.tree = HexagonCover.NBand.M8300_8500.SplitData.node2196 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2197
  · rfl

def B2195 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B2196, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2195 : B2195.tree = HexagonCover.NBand.M8300_8500.SplitData.node2195 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2196
  · rfl

def B2150 : Block := .branch 108 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B2151, B2195, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq2150 : B2150.tree = HexagonCover.NBand.M8300_8500.SplitData.node2150 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2151
  · exact treeEq2195
  · rfl
  · rfl

def B2203 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2203 : B2203.tree = HexagonCover.NBand.M8300_8500.SplitData.node2203 := by
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

def B2202 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2203, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq2202 : B2202.tree = HexagonCover.NBand.M8300_8500.SplitData.node2202 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2203
  · rfl
  · rfl
  · rfl

def B2201 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400323542557505178544306689315037511744] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B2202]
theorem treeEq2201 : B2201.tree = HexagonCover.NBand.M8300_8500.SplitData.node2201 := by
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
  · exact treeEq2202

def B2200 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922807869075946403443013495790501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2201, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2200 : B2200.tree = HexagonCover.NBand.M8300_8500.SplitData.node2200 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2201
  · rfl

def B2149 : Block := .branch 100 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B2150, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B2200]
theorem treeEq2149 : B2149.tree = HexagonCover.NBand.M8300_8500.SplitData.node2149 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2150
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2200

theorem accepted2149 : B2149.accepted = true := by decide +kernel
theorem checked2149 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2149 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2149]
  exact B2149.sound accepted2149
#print axioms checked2149

end HexagonCover.NBand.M8300_8500.SplitTree.Run0029
