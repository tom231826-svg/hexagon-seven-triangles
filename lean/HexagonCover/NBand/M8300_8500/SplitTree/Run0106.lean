import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0106
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B7715 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 83808349891103296941472103047282533479150345499705408] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1744).pointIds 1744)]
theorem treeEq7715 : B7715.tree = HexagonCover.NBand.M8300_8500.SplitData.node7715 := by
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

def B7714 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 83811272894377958747308510416947966045189657364791360] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7715, (.leaf 6 (Common.fact 1743).pointIds 1743)]
theorem treeEq7714 : B7714.tree = HexagonCover.NBand.M8300_8500.SplitData.node7714 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7715
  · rfl

def B7713 : Block := .branch 161 ![385, 144115188075857410, 95780971304118053647396689196936834551932804082440196, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 83808349891103296941472103047282533479150345499705408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1722).pointIds 1722), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7714]
theorem treeEq7713 : B7713.tree = HexagonCover.NBand.M8300_8500.SplitData.node7713 := by
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
  · exact treeEq7714

def B7712 : Block := .branch 176 ![385, 146507725377897986, 42510575761608945965060, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 83808349891125080329867026248607681069254219786616896] ![(.leaf 0 (Common.fact 1738).pointIds 1738), (.leaf 1 (Common.fact 1739).pointIds 1739), B7713, (.leaf 3 (Common.fact 1718).pointIds 1718), (.leaf 4 (Common.fact 1740).pointIds 1740), (.leaf 5 (Common.fact 1720).pointIds 1720), (.leaf 6 (Common.fact 1741).pointIds 1741)]
theorem treeEq7712 : B7712.tree = HexagonCover.NBand.M8300_8500.SplitData.node7712 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7713
  · rfl
  · rfl
  · rfl
  · rfl

def B7711 : Block := .branch 170 ![385, 146507725377897986, 42510575761608945965060, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 83808349891125080329867026248607681069254219786616896] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7712, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1737).pointIds 1737)]
theorem treeEq7711 : B7711.tree = HexagonCover.NBand.M8300_8500.SplitData.node7711 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7712
  · rfl
  · rfl
  · rfl

def B7710 : Block := .branch 174 ![385, 146507725377897986, 42510575761608945965060, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 59863107065095566918017853949384100075211421002498112] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B7711]
theorem treeEq7710 : B7710.tree = HexagonCover.NBand.M8300_8500.SplitData.node7710 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7711

def B7709 : Block := .branch 139 ![385, 146507725377897986, 42510575761608945965060, 81208866577120946033382549118984, 98320, 393248, 59863107065095566918017853949384100075211421002498112] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7710, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1749).pointIds 1749)]
theorem treeEq7709 : B7709.tree = HexagonCover.NBand.M8300_8500.SplitData.node7709 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7710
  · rfl
  · rfl

def B7708 : Block := .branch 147 ![385, 146507725377897986, 42510575761608945965060, 81208866577120946033382549118984, 98320, 393248, 59863107065095566918017853949384100075211421002498112] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7709, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1748).pointIds 1748)]
theorem treeEq7708 : B7708.tree = HexagonCover.NBand.M8300_8500.SplitData.node7708 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7709
  · rfl
  · rfl

def B7707 : Block := .branch 148 ![385, 146507725377897986, 42510575761608945965060, 81208866577120946033382549118984, 98320, 393248, 59863107065095566918017853949384100075211421002498112] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7708, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1747).pointIds 1747)]
theorem treeEq7707 : B7707.tree = HexagonCover.NBand.M8300_8500.SplitData.node7707 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7708
  · rfl
  · rfl

def B7706 : Block := .branch 173 ![604462909807314587353473, 146507725377897986, 42510575761608945965060, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7707]
theorem treeEq7706 : B7706.tree = HexagonCover.NBand.M8300_8500.SplitData.node7706 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7707

def B7717 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945242826029513411849172299223580994042798784217104, 393248, 47890485652080810212093267800376772487997336197791808] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1751).pointIds 1751), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1752).pointIds 1752)]
theorem treeEq7717 : B7717.tree = HexagonCover.NBand.M8300_8500.SplitData.node7717 := by
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

def B7716 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 47890485652080810212093267800376772487997336197791808] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7717, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1750).pointIds 1750)]
theorem treeEq7716 : B7716.tree = HexagonCover.NBand.M8300_8500.SplitData.node7716 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7717
  · rfl
  · rfl

def B7705 : Block := .branch 79 ![385, 218565319415825922, 42510575761608945965060, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![B7706, (.leaf 1 (Common.fact 1730).pointIds 1730), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7716]
theorem treeEq7705 : B7705.tree = HexagonCover.NBand.M8300_8500.SplitData.node7705 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7706
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7716

def B7719 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945242826029513411849172299223580994042798784217104, 393248, 47890485652080810212093267799923425305641850257276992] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1754).pointIds 1754)]
theorem treeEq7719 : B7719.tree = HexagonCover.NBand.M8300_8500.SplitData.node7719 := by
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

def B7718 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799923425305641850257276992] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7719, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1753).pointIds 1753)]
theorem treeEq7718 : B7718.tree = HexagonCover.NBand.M8300_8500.SplitData.node7718 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7719
  · rfl
  · rfl

def B7704 : Block := .branch 77 ![385, 218565319415825922, 42510575761608945965060, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 163).pointIds 163), B7705, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7718]
theorem treeEq7704 : B7704.tree = HexagonCover.NBand.M8300_8500.SplitData.node7704 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7705
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7718

def B7721 : Block := .branch 141 ![385, 1538, 6148, 24584, 23945242826029513411849172299223580994042798784217104, 393248, 21783388394923201362926521967381203910720] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), (.leaf 4 (Common.fact 1756).pointIds 1756), (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 1757).pointIds 1757)]
theorem treeEq7721 : B7721.tree = HexagonCover.NBand.M8300_8500.SplitData.node7721 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7720 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 21783388394923201362926521967381203910720] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7721, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1755).pointIds 1755)]
theorem treeEq7720 : B7720.tree = HexagonCover.NBand.M8300_8500.SplitData.node7720 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7721
  · rfl
  · rfl

def B7703 : Block := .branch 75 ![385, 218565319415825922, 4731643898651784255492, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7704, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7720]
theorem treeEq7703 : B7703.tree = HexagonCover.NBand.M8300_8500.SplitData.node7703 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7704
  · rfl
  · rfl
  · rfl
  · exact treeEq7720

theorem accepted7703 : B7703.accepted = true := by decide +kernel
theorem checked7703 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7703 (maskNeeds ![385, 218565319415825922, 4731643898651784255492, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720]) := by
  rw [← treeEq7703]
  exact B7703.sound accepted7703
#print axioms checked7703

def Tip7700_7703 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7703 ![385, 218565319415825922, 4731643898651784255492, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] checked7703
def B7723 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945242826029513411849172299223580994042798784217104, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7723 : B7723.tree = HexagonCover.NBand.M8300_8500.SplitData.node7723 := by
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

def B7722 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7723, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7722 : B7722.tree = HexagonCover.NBand.M8300_8500.SplitData.node7722 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7723
  · rfl
  · rfl

def B7702 : Block := .branch 66 ![385, 218565319415825922, 23639556574204074661892, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 148).pointIds 148), Tip7700_7703, (.leaf 2 (Common.fact 1556).pointIds 1556), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7722]
theorem treeEq7702 : B7702.tree = HexagonCover.NBand.M8300_8500.SplitData.node7702 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7722

def B7730 : Block := .branch 138 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 47890485652091693930922913147264674479074784159727680] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 1425).pointIds 1425), (.leaf 4 (Common.fact 1760).pointIds 1760), (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1761).pointIds 1761)]
theorem treeEq7730 : B7730.tree = HexagonCover.NBand.M8300_8500.SplitData.node7730 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7729 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 47890485652091693930922913147264674479074784159727680] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7730, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1759).pointIds 1759)]
theorem treeEq7729 : B7729.tree = HexagonCover.NBand.M8300_8500.SplitData.node7729 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7730
  · rfl
  · rfl

def B7728 : Block := .branch 97 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 47890485652091693930922754690939645950399597071827008] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 1418).pointIds 1418), (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), B7729]
theorem treeEq7728 : B7728.tree = HexagonCover.NBand.M8300_8500.SplitData.node7728 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7729

def B7727 : Block := .branch 133 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 1412).pointIds 1412), (.leaf 1 (Common.fact 1413).pointIds 1413), (.leaf 2 (Common.fact 1414).pointIds 1414), (.leaf 3 (Common.fact 1415).pointIds 1415), (.leaf 4 (Common.fact 1758).pointIds 1758), (.leaf 5 (Common.fact 1417).pointIds 1417), B7728]
theorem treeEq7727 : B7727.tree = HexagonCover.NBand.M8300_8500.SplitData.node7727 := by
  change Tree.branch (133 : Fin 177) _ = Tree.branch (133 : Fin 177) _
  apply congrArg (Tree.branch (133 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7728

def B7726 : Block := .branch 162 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1671).pointIds 1671), (.leaf 5 (Common.fact 358).pointIds 358), B7727]
theorem treeEq7726 : B7726.tree = HexagonCover.NBand.M8300_8500.SplitData.node7726 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7727

def B7725 : Block := .branch 146 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7726, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7725 : B7725.tree = HexagonCover.NBand.M8300_8500.SplitData.node7725 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7726
  · rfl
  · rfl

def B7724 : Block := .branch 170 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7725]
theorem treeEq7724 : B7724.tree = HexagonCover.NBand.M8300_8500.SplitData.node7724 := by
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
  · exact treeEq7725

def B7701 : Block := .branch 74 ![385, 218565319415825922, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), B7702, B7724, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7701 : B7701.tree = HexagonCover.NBand.M8300_8500.SplitData.node7701 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7702
  · exact treeEq7724
  · rfl
  · rfl
  · rfl

def B7737 : Block := .branch 138 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 47890485652091693930922913147264674479074784159727680] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 1434).pointIds 1434), (.leaf 4 (Common.fact 1760).pointIds 1760), (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1761).pointIds 1761)]
theorem treeEq7737 : B7737.tree = HexagonCover.NBand.M8300_8500.SplitData.node7737 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7736 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 47890485652091693930922913147264674479074784159727680] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7737, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1759).pointIds 1759)]
theorem treeEq7736 : B7736.tree = HexagonCover.NBand.M8300_8500.SplitData.node7736 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7737
  · rfl
  · rfl

def B7735 : Block := .branch 97 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 47890485652091693930922754690939645950399597071827008] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 1431).pointIds 1431), (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), B7736]
theorem treeEq7735 : B7735.tree = HexagonCover.NBand.M8300_8500.SplitData.node7735 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7736

def B7734 : Block := .branch 133 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 1412).pointIds 1412), (.leaf 1 (Common.fact 1413).pointIds 1413), (.leaf 2 (Common.fact 1414).pointIds 1414), (.leaf 3 (Common.fact 1415).pointIds 1415), (.leaf 4 (Common.fact 1758).pointIds 1758), (.leaf 5 (Common.fact 1417).pointIds 1417), B7735]
theorem treeEq7734 : B7734.tree = HexagonCover.NBand.M8300_8500.SplitData.node7734 := by
  change Tree.branch (133 : Fin 177) _ = Tree.branch (133 : Fin 177) _
  apply congrArg (Tree.branch (133 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7735

def B7733 : Block := .branch 162 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1671).pointIds 1671), (.leaf 5 (Common.fact 358).pointIds 358), B7734]
theorem treeEq7733 : B7733.tree = HexagonCover.NBand.M8300_8500.SplitData.node7733 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7734

def B7732 : Block := .branch 146 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7733, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7732 : B7732.tree = HexagonCover.NBand.M8300_8500.SplitData.node7732 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7733
  · rfl
  · rfl

def B7731 : Block := .branch 170 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 47890485652080804895181284660108817962961780489060416] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7732]
theorem treeEq7731 : B7731.tree = HexagonCover.NBand.M8300_8500.SplitData.node7731 := by
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
  · exact treeEq7732

def B7700 : Block := .branch 73 ![385, 218565319415825922, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), B7701, B7731, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7700 : B7700.tree = HexagonCover.NBand.M8300_8500.SplitData.node7700 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7701
  · exact treeEq7731
  · rfl
  · rfl
  · rfl

theorem accepted7700 : B7700.accepted = true := by decide +kernel
theorem checked7700 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7700 (maskNeeds ![385, 218565319415825922, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720]) := by
  rw [← treeEq7700]
  exact B7700.sound accepted7700
#print axioms checked7700

def Tip7684_7700 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7700 ![385, 218565319415825922, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] checked7700
def B7696 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 83808349891103296941472103047282533479150345499705408] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1744).pointIds 1744)]
theorem treeEq7696 : B7696.tree = HexagonCover.NBand.M8300_8500.SplitData.node7696 := by
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

def B7695 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 83811272894377958747308510416947966045189657364791360] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7696, (.leaf 6 (Common.fact 1743).pointIds 1743)]
theorem treeEq7695 : B7695.tree = HexagonCover.NBand.M8300_8500.SplitData.node7695 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7696
  · rfl

def B7694 : Block := .branch 161 ![385, 144115188075857410, 95780971304118053647396689196899074066813920630282244, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 83808349891103296941472103047282533479150345499705408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1742).pointIds 1742), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7695]
theorem treeEq7694 : B7694.tree = HexagonCover.NBand.M8300_8500.SplitData.node7694 := by
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
  · exact treeEq7695

def B7693 : Block := .branch 176 ![385, 146507725377897986, 4750090642725493807108, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 83808349891125080329867026248607681069254219786616896] ![(.leaf 0 (Common.fact 1738).pointIds 1738), (.leaf 1 (Common.fact 1739).pointIds 1739), B7694, (.leaf 3 (Common.fact 1718).pointIds 1718), (.leaf 4 (Common.fact 1740).pointIds 1740), (.leaf 5 (Common.fact 1720).pointIds 1720), (.leaf 6 (Common.fact 1741).pointIds 1741)]
theorem treeEq7693 : B7693.tree = HexagonCover.NBand.M8300_8500.SplitData.node7693 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7694
  · rfl
  · rfl
  · rfl
  · rfl

def B7692 : Block := .branch 170 ![385, 146507725377897986, 4750090642725493807108, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 83808349891125080329867026248607681069254219786616896] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7693, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1737).pointIds 1737)]
theorem treeEq7692 : B7692.tree = HexagonCover.NBand.M8300_8500.SplitData.node7692 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7693
  · rfl
  · rfl
  · rfl

def B7691 : Block := .branch 175 ![385, 1461501637330902918203684832716429527381310440962, 4750090642725493807108, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 1732).pointIds 1732), (.leaf 1 (Common.fact 1733).pointIds 1733), (.leaf 2 (Common.fact 1734).pointIds 1734), (.leaf 3 (Common.fact 1735).pointIds 1735), (.leaf 4 (Common.fact 1736).pointIds 1736), (.leaf 5 (Common.fact 1646).pointIds 1646), B7692]
theorem treeEq7691 : B7691.tree = HexagonCover.NBand.M8300_8500.SplitData.node7691 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7692

def B7690 : Block := .branch 160 ![385, 146507725377897986, 4750090642725493807108, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 347).pointIds 347), B7691, (.leaf 2 (Common.fact 1550).pointIds 1550), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1571).pointIds 1571)]
theorem treeEq7690 : B7690.tree = HexagonCover.NBand.M8300_8500.SplitData.node7690 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7691
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7689 : Block := .branch 174 ![385, 146507725377897986, 4750090642725493807108, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B7690]
theorem treeEq7689 : B7689.tree = HexagonCover.NBand.M8300_8500.SplitData.node7689 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7690

def B7688 : Block := .branch 139 ![385, 146507725377897986, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7689, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1570).pointIds 1570)]
theorem treeEq7688 : B7688.tree = HexagonCover.NBand.M8300_8500.SplitData.node7688 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7689
  · rfl
  · rfl

def B7687 : Block := .branch 147 ![385, 146507725377897986, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7688, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1569).pointIds 1569)]
theorem treeEq7687 : B7687.tree = HexagonCover.NBand.M8300_8500.SplitData.node7687 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7688
  · rfl
  · rfl

def B7686 : Block := .branch 148 ![385, 146507725377897986, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7687, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1568).pointIds 1568)]
theorem treeEq7686 : B7686.tree = HexagonCover.NBand.M8300_8500.SplitData.node7686 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7687
  · rfl
  · rfl

def B7685 : Block := .branch 173 ![576460752303423873, 146507725377897986, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7686]
theorem treeEq7685 : B7685.tree = HexagonCover.NBand.M8300_8500.SplitData.node7685 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7686

def B7739 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945242826029513411849172299223580994042798784217104, 393248, 47890485652080810212093267799772899874000380316090432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1751).pointIds 1751), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1763).pointIds 1763)]
theorem treeEq7739 : B7739.tree = HexagonCover.NBand.M8300_8500.SplitData.node7739 := by
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

def B7738 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 47890485652080810212093267799772899874000380316090432] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7739, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1762).pointIds 1762)]
theorem treeEq7738 : B7738.tree = HexagonCover.NBand.M8300_8500.SplitData.node7738 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7739
  · rfl
  · rfl

def B7699 : Block := .branch 69 ![385, 218565319415825922, 4750090642725493807108, 81208866577120946033382549118984, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![Tip7684_7700, (.leaf 1 (Common.fact 1746).pointIds 1746), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7738]
theorem treeEq7699 : B7699.tree = HexagonCover.NBand.M8300_8500.SplitData.node7699 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7738

def B7741 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945242826029513411849172299223580994042798784217104, 393248, 47890485652080810212093267799772457152142611286851648] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1765).pointIds 1765), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1766).pointIds 1766)]
theorem treeEq7741 : B7741.tree = HexagonCover.NBand.M8300_8500.SplitData.node7741 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7740 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81248480658378078202179321094152, 98320, 393248, 47890485652080810212093267799772457152142611286851648] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7741, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1764).pointIds 1764)]
theorem treeEq7740 : B7740.tree = HexagonCover.NBand.M8300_8500.SplitData.node7740 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7741
  · rfl
  · rfl

def B7698 : Block := .branch 67 ![385, 218565319415825922, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 47890485652080810212093267799772309578190021610438720] ![(.leaf 0 (Common.fact 153).pointIds 153), B7699, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7740]
theorem treeEq7698 : B7698.tree = HexagonCover.NBand.M8300_8500.SplitData.node7698 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7699
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7740

def B7697 : Block := .branch 175 ![385, 1083256447870961154, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1732).pointIds 1732), (.leaf 1 (Common.fact 1745).pointIds 1745), (.leaf 2 (Common.fact 1734).pointIds 1734), (.leaf 3 (Common.fact 1735).pointIds 1735), (.leaf 4 (Common.fact 1736).pointIds 1736), (.leaf 5 (Common.fact 1646).pointIds 1646), B7698]
theorem treeEq7697 : B7697.tree = HexagonCover.NBand.M8300_8500.SplitData.node7697 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7698

def B7684 : Block := .branch 59 ![385, 506795695567537666, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![B7685, B7697, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7684 : B7684.tree = HexagonCover.NBand.M8300_8500.SplitData.node7684 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7685
  · exact treeEq7697
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7684 : B7684.accepted = true := by decide +kernel
theorem checked7684 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7684 (maskNeeds ![385, 506795695567537666, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq7684]
  exact B7684.sound accepted7684
#print axioms checked7684

def B7756 : Block := .branch 141 ![385, 1538, 6148, 24584, 23945242915232494205971664865366454084636244808138768, 393248, 5846006581990718897224831861128026255580395470912] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), (.leaf 4 (Common.fact 1776).pointIds 1776), (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 1777).pointIds 1777)]
theorem treeEq7756 : B7756.tree = HexagonCover.NBand.M8300_8500.SplitData.node7756 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7755 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 89202980794122492566142873090593446024019984, 393248, 5846006581990718897224831861128026255580395470912] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7756, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1775).pointIds 1775)]
theorem treeEq7755 : B7755.tree = HexagonCover.NBand.M8300_8500.SplitData.node7755 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7756
  · rfl
  · rfl

def B7754 : Block := .branch 75 ![385, 144115188075857410, 4750126671522512771076, 79228162514264337593543974920, 89202980794122492566142873090593446024019984, 393248, 5846006581990718897224831823349094392623233761344] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), (.leaf 2 (Common.fact 1562).pointIds 1562), (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7755]
theorem treeEq7754 : B7754.tree = HexagonCover.NBand.M8300_8500.SplitData.node7754 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7755

def B7753 : Block := .branch 82 ![385, 144115188075857410, 4750126671522512771076, 79228162514264337593543974920, 89202980794122492566142873090593446024019984, 393248, 5846006581990718897224831823349094392623233761344] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), (.leaf 2 (Common.fact 1561).pointIds 1561), B7754, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq7753 : B7753.tree = HexagonCover.NBand.M8300_8500.SplitData.node7753 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7754
  · rfl
  · rfl
  · rfl

def B7752 : Block := .branch 85 ![385, 144115188075857410, 4750126671522512771076, 79228162514264337593543974920, 89202980794122492566142873090593446024019984, 393248, 5846006581996035809207971486840709620864355139648] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 1557).pointIds 1557), B7753, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7752 : B7752.tree = HexagonCover.NBand.M8300_8500.SplitData.node7752 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7753
  · rfl
  · rfl
  · rfl

def B7751 : Block := .branch 165 ![385, 144115188075857410, 4750126671522512771076, 79228162514264337593543974920, 1516450673500082373624428842540088582406766608, 393248, 5846006581996035809207971486840709620864355139648] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7752, (.leaf 0 [] 0)]
theorem treeEq7751 : B7751.tree = HexagonCover.NBand.M8300_8500.SplitData.node7751 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7752
  · rfl

def B7750 : Block := .branch 167 ![385, 144115188075857410, 4750126671522512771076, 79228162514264337593543974920, 1516450673500082373624428842540088582406766608, 393248, 5846006581996035809207971486840709620864355139648] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7751, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7750 : B7750.tree = HexagonCover.NBand.M8300_8500.SplitData.node7750 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7751
  · rfl

def B7749 : Block := .branch 150 ![385, 144115188075857410, 4750126671522512771076, 79228162514264337593543974920, 89202980794122492566142873090593446024019984, 393248, 5846006581996035809208126229345620293398717530176] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7750, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1774).pointIds 1774)]
theorem treeEq7749 : B7749.tree = HexagonCover.NBand.M8300_8500.SplitData.node7749 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7750
  · rfl
  · rfl

def B7748 : Block := .branch 87 ![385, 144115188075857410, 4750126671522512771076, 95780971304118053647396768425056838240508788680450056, 89202980794122492566142873090593446024019984, 393248, 5846006581996035809207971486840709620864355139648] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), (.leaf 2 (Common.fact 1772).pointIds 1772), (.leaf 3 (Common.fact 1773).pointIds 1773), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), B7749]
theorem treeEq7748 : B7748.tree = HexagonCover.NBand.M8300_8500.SplitData.node7748 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7749

def B7747 : Block := .branch 133 ![385, 144115188075857410, 4750126671522512771076, 95780971304118053647396768425056838240508788680450056, 89202980794122492566142873090593446024019984, 393248, 5846006571107000067737940656012722183047772373056] ![(.leaf 0 (Common.fact 1412).pointIds 1412), (.leaf 1 (Common.fact 1413).pointIds 1413), (.leaf 2 (Common.fact 1414).pointIds 1414), (.leaf 3 (Common.fact 1415).pointIds 1415), (.leaf 4 (Common.fact 1758).pointIds 1758), (.leaf 5 (Common.fact 1417).pointIds 1417), B7748]
theorem treeEq7747 : B7747.tree = HexagonCover.NBand.M8300_8500.SplitData.node7747 := by
  change Tree.branch (133 : Fin 177) _ = Tree.branch (133 : Fin 177) _
  apply congrArg (Tree.branch (133 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7748

def B7746 : Block := .branch 162 ![385, 144115188075857410, 4750126671522512771076, 95780971304118053647396768425056838240508788680450056, 89202980794122492566142873090593446024019984, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1771).pointIds 1771), (.leaf 4 (Common.fact 1671).pointIds 1671), (.leaf 5 (Common.fact 358).pointIds 358), B7747]
theorem treeEq7746 : B7746.tree = HexagonCover.NBand.M8300_8500.SplitData.node7746 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7747

def B7745 : Block := .branch 146 ![385, 144115188075857410, 4750126671522512771076, 95780971304118053647396768425056838240508788680450056, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1770).pointIds 1770), B7746, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7745 : B7745.tree = HexagonCover.NBand.M8300_8500.SplitData.node7745 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7746
  · rfl
  · rfl

def B7744 : Block := .branch 161 ![385, 144115188075857410, 4750126671522512771076, 95780971304118053647396768425056838240508788680450056, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1558).pointIds 1558), (.leaf 3 (Common.fact 1769).pointIds 1769), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7745]
theorem treeEq7744 : B7744.tree = HexagonCover.NBand.M8300_8500.SplitData.node7744 := by
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
  · exact treeEq7745

def B7743 : Block := .branch 170 ![385, 144115188075857410, 4750126671522512771076, 95780971304118053647396768425056838240508788680450056, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1768).pointIds 1768), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7744]
theorem treeEq7743 : B7743.tree = HexagonCover.NBand.M8300_8500.SplitData.node7743 := by
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
  · exact treeEq7744

def B7742 : Block := .branch 176 ![385, 146507725377897986, 4750126671522512771076, 79228162514264337593543974920, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1738).pointIds 1738), (.leaf 1 (Common.fact 1739).pointIds 1739), (.leaf 2 (Common.fact 1767).pointIds 1767), B7743, (.leaf 4 (Common.fact 1740).pointIds 1740), (.leaf 5 (Common.fact 1720).pointIds 1720), (.leaf 6 (Common.fact 1741).pointIds 1741)]
theorem treeEq7742 : B7742.tree = HexagonCover.NBand.M8300_8500.SplitData.node7742 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7743
  · rfl
  · rfl
  · rfl

theorem accepted7742 : B7742.accepted = true := by decide +kernel
theorem checked7742 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7742 (maskNeeds ![385, 146507725377897986, 4750126671522512771076, 79228162514264337593543974920, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq7742]
  exact B7742.sound accepted7742
#print axioms checked7742

end HexagonCover.NBand.M8300_8500.SplitTree.Run0106
