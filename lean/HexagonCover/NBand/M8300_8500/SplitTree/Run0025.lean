import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0025
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B1882 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq1882 : B1882.tree = HexagonCover.NBand.M8300_8500.SplitData.node1882 := by
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
  · rfl

def B1881 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1882, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1881 : B1881.tree = HexagonCover.NBand.M8300_8500.SplitData.node1881 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1882
  · rfl
  · rfl

def B1880 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1881, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1880 : B1880.tree = HexagonCover.NBand.M8300_8500.SplitData.node1880 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1881
  · rfl
  · rfl

def B1879 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1880, (.leaf 0 [] 0)]
theorem treeEq1879 : B1879.tree = HexagonCover.NBand.M8300_8500.SplitData.node1879 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1880
  · rfl

def B1878 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1879, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1878 : B1878.tree = HexagonCover.NBand.M8300_8500.SplitData.node1878 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1879
  · rfl

def B1877 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1878, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1877 : B1877.tree = HexagonCover.NBand.M8300_8500.SplitData.node1877 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1878
  · rfl
  · rfl

def B1876 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1877, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq1876 : B1876.tree = HexagonCover.NBand.M8300_8500.SplitData.node1876 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1877
  · rfl
  · rfl
  · rfl

def B1875 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 42535295865117307932921825928971419680, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B1876]
theorem treeEq1875 : B1875.tree = HexagonCover.NBand.M8300_8500.SplitData.node1875 := by
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
  · exact treeEq1876

def B1889 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1889 : B1889.tree = HexagonCover.NBand.M8300_8500.SplitData.node1889 := by
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
  · rfl

def B1888 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1889, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1888 : B1888.tree = HexagonCover.NBand.M8300_8500.SplitData.node1888 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1889
  · rfl
  · rfl

def B1887 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1888, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1887 : B1887.tree = HexagonCover.NBand.M8300_8500.SplitData.node1887 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1888
  · rfl
  · rfl

def B1886 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1887, (.leaf 0 [] 0)]
theorem treeEq1886 : B1886.tree = HexagonCover.NBand.M8300_8500.SplitData.node1886 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1887
  · rfl

def B1885 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1886, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1885 : B1885.tree = HexagonCover.NBand.M8300_8500.SplitData.node1885 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1886
  · rfl

def B1884 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1885, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1884 : B1884.tree = HexagonCover.NBand.M8300_8500.SplitData.node1884 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1885
  · rfl
  · rfl

def B1883 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1884, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1883 : B1883.tree = HexagonCover.NBand.M8300_8500.SplitData.node1883 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1884
  · rfl
  · rfl
  · rfl

def B1874 : Block := .branch 125 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B1875, B1883]
theorem treeEq1874 : B1874.tree = HexagonCover.NBand.M8300_8500.SplitData.node1874 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1875
  · exact treeEq1883

theorem accepted1874 : B1874.accepted = true := by decide +kernel
theorem checked1874 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1874 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1874]
  exact B1874.sound accepted1874
#print axioms checked1874

def B1916 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq1916 : B1916.tree = HexagonCover.NBand.M8300_8500.SplitData.node1916 := by
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
  · rfl

def B1915 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1916, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1915 : B1915.tree = HexagonCover.NBand.M8300_8500.SplitData.node1915 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1916
  · rfl
  · rfl

def B1914 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1915, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1914 : B1914.tree = HexagonCover.NBand.M8300_8500.SplitData.node1914 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1915
  · rfl
  · rfl

def B1913 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1914, (.leaf 0 [] 0)]
theorem treeEq1913 : B1913.tree = HexagonCover.NBand.M8300_8500.SplitData.node1913 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1914
  · rfl

def B1912 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1913, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1912 : B1912.tree = HexagonCover.NBand.M8300_8500.SplitData.node1912 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1913
  · rfl

def B1911 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1912, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1911 : B1911.tree = HexagonCover.NBand.M8300_8500.SplitData.node1911 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1912
  · rfl
  · rfl

def B1910 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1911, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq1910 : B1910.tree = HexagonCover.NBand.M8300_8500.SplitData.node1910 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1911
  · rfl
  · rfl
  · rfl

def B1909 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B1910]
theorem treeEq1909 : B1909.tree = HexagonCover.NBand.M8300_8500.SplitData.node1909 := by
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
  · exact treeEq1910

def B1923 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1923 : B1923.tree = HexagonCover.NBand.M8300_8500.SplitData.node1923 := by
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
  · rfl

def B1922 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1923, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1922 : B1922.tree = HexagonCover.NBand.M8300_8500.SplitData.node1922 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1923
  · rfl
  · rfl

def B1921 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1922, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1921 : B1921.tree = HexagonCover.NBand.M8300_8500.SplitData.node1921 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1922
  · rfl
  · rfl

def B1920 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1921, (.leaf 0 [] 0)]
theorem treeEq1920 : B1920.tree = HexagonCover.NBand.M8300_8500.SplitData.node1920 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1921
  · rfl

def B1919 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1920, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1919 : B1919.tree = HexagonCover.NBand.M8300_8500.SplitData.node1919 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1920
  · rfl

def B1918 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1919, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1918 : B1918.tree = HexagonCover.NBand.M8300_8500.SplitData.node1918 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1919
  · rfl
  · rfl

def B1917 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1918, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1917 : B1917.tree = HexagonCover.NBand.M8300_8500.SplitData.node1917 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1918
  · rfl
  · rfl
  · rfl

def B1908 : Block := .branch 125 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B1909, B1917]
theorem treeEq1908 : B1908.tree = HexagonCover.NBand.M8300_8500.SplitData.node1908 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1909
  · exact treeEq1917

theorem accepted1908 : B1908.accepted = true := by decide +kernel
theorem checked1908 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1908 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1908]
  exact B1908.sound accepted1908
#print axioms checked1908

def Tip1906_1908 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1908 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] checked1908
def B1935 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq1935 : B1935.tree = HexagonCover.NBand.M8300_8500.SplitData.node1935 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1934 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1935, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1934 : B1934.tree = HexagonCover.NBand.M8300_8500.SplitData.node1934 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1935
  · rfl
  · rfl

def B1933 : Block := .branch 166 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B1934, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1933 : B1933.tree = HexagonCover.NBand.M8300_8500.SplitData.node1933 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1934
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1932 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1933, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq1932 : B1932.tree = HexagonCover.NBand.M8300_8500.SplitData.node1932 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1933
  · rfl
  · rfl
  · rfl
  · rfl

def B1931 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1932, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1931 : B1931.tree = HexagonCover.NBand.M8300_8500.SplitData.node1931 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1932
  · rfl
  · rfl

def B1930 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1931, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1930 : B1930.tree = HexagonCover.NBand.M8300_8500.SplitData.node1930 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1931
  · rfl
  · rfl

def B1929 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1930, (.leaf 0 [] 0)]
theorem treeEq1929 : B1929.tree = HexagonCover.NBand.M8300_8500.SplitData.node1929 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1930
  · rfl

def B1928 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1929, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1928 : B1928.tree = HexagonCover.NBand.M8300_8500.SplitData.node1928 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1929
  · rfl

def B1927 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1928, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1927 : B1927.tree = HexagonCover.NBand.M8300_8500.SplitData.node1927 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1928
  · rfl
  · rfl

def B1926 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1927, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1926 : B1926.tree = HexagonCover.NBand.M8300_8500.SplitData.node1926 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1927
  · rfl
  · rfl
  · rfl

def B1925 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422335658661502629357934307808096157728, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B1926]
theorem treeEq1925 : B1925.tree = HexagonCover.NBand.M8300_8500.SplitData.node1925 := by
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
  · exact treeEq1926

def B1924 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1925, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1924 : B1924.tree = HexagonCover.NBand.M8300_8500.SplitData.node1924 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1925
  · rfl

def B1907 : Block := .branch 121 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip1906_1908, (.leaf 5 (Common.fact 256).pointIds 256), B1924]
theorem treeEq1907 : B1907.tree = HexagonCover.NBand.M8300_8500.SplitData.node1907 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1924

def B1940 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1940 : B1940.tree = HexagonCover.NBand.M8300_8500.SplitData.node1940 := by
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

def B1939 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1940, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1939 : B1939.tree = HexagonCover.NBand.M8300_8500.SplitData.node1939 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1940
  · rfl

def B1938 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1939]
theorem treeEq1938 : B1938.tree = HexagonCover.NBand.M8300_8500.SplitData.node1938 := by
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
  · exact treeEq1939

def B1937 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1938, (.leaf 0 [] 0)]
theorem treeEq1937 : B1937.tree = HexagonCover.NBand.M8300_8500.SplitData.node1937 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1938
  · rfl

def B1936 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1937, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1936 : B1936.tree = HexagonCover.NBand.M8300_8500.SplitData.node1936 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1937
  · rfl

def B1906 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1907, B1936, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1906 : B1906.tree = HexagonCover.NBand.M8300_8500.SplitData.node1906 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1907
  · exact treeEq1936
  · rfl
  · rfl

theorem accepted1906 : B1906.accepted = true := by decide +kernel
theorem checked1906 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1906 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1906]
  exact B1906.sound accepted1906
#print axioms checked1906

def Tip1871_1874 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1874 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280] checked1874
def Tip1871_1906 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1906 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] checked1906
def B1900 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq1900 : B1900.tree = HexagonCover.NBand.M8300_8500.SplitData.node1900 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1899 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1900, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1899 : B1899.tree = HexagonCover.NBand.M8300_8500.SplitData.node1899 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1900
  · rfl
  · rfl

def B1898 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1899, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq1898 : B1898.tree = HexagonCover.NBand.M8300_8500.SplitData.node1898 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1899
  · rfl
  · rfl
  · rfl
  · rfl

def B1897 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1898, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1897 : B1897.tree = HexagonCover.NBand.M8300_8500.SplitData.node1897 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1898
  · rfl
  · rfl

def B1896 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1897, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1896 : B1896.tree = HexagonCover.NBand.M8300_8500.SplitData.node1896 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1897
  · rfl
  · rfl

def B1895 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1896, (.leaf 0 [] 0)]
theorem treeEq1895 : B1895.tree = HexagonCover.NBand.M8300_8500.SplitData.node1895 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1896
  · rfl

def B1894 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1895, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1894 : B1894.tree = HexagonCover.NBand.M8300_8500.SplitData.node1894 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1895
  · rfl

def B1893 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1894, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1893 : B1893.tree = HexagonCover.NBand.M8300_8500.SplitData.node1893 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1894
  · rfl
  · rfl

def B1892 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1893, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1892 : B1892.tree = HexagonCover.NBand.M8300_8500.SplitData.node1892 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1893
  · rfl
  · rfl
  · rfl

def B1891 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B1892]
theorem treeEq1891 : B1891.tree = HexagonCover.NBand.M8300_8500.SplitData.node1891 := by
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
  · exact treeEq1892

def B1890 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1891, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1890 : B1890.tree = HexagonCover.NBand.M8300_8500.SplitData.node1890 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1891
  · rfl

def B1873 : Block := .branch 121 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip1871_1874, (.leaf 5 (Common.fact 256).pointIds 256), B1890]
theorem treeEq1873 : B1873.tree = HexagonCover.NBand.M8300_8500.SplitData.node1873 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1890

def B1905 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1905 : B1905.tree = HexagonCover.NBand.M8300_8500.SplitData.node1905 := by
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

def B1904 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1905, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1904 : B1904.tree = HexagonCover.NBand.M8300_8500.SplitData.node1904 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1905
  · rfl

def B1903 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1904]
theorem treeEq1903 : B1903.tree = HexagonCover.NBand.M8300_8500.SplitData.node1903 := by
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
  · exact treeEq1904

def B1902 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1903, (.leaf 0 [] 0)]
theorem treeEq1902 : B1902.tree = HexagonCover.NBand.M8300_8500.SplitData.node1902 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1903
  · rfl

def B1901 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1902, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1901 : B1901.tree = HexagonCover.NBand.M8300_8500.SplitData.node1901 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1902
  · rfl

def B1872 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1873, B1901, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1872 : B1872.tree = HexagonCover.NBand.M8300_8500.SplitData.node1872 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1873
  · exact treeEq1901
  · rfl
  · rfl

def B1871 : Block := .branch 115 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B1872, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), Tip1871_1906, (.leaf 0 [] 0)]
theorem treeEq1871 : B1871.tree = HexagonCover.NBand.M8300_8500.SplitData.node1871 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1872
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1871 : B1871.accepted = true := by decide +kernel
theorem checked1871 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1871 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1871]
  exact B1871.sound accepted1871
#print axioms checked1871

end HexagonCover.NBand.M8300_8500.SplitTree.Run0025
