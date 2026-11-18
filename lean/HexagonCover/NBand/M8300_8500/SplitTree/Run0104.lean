import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0103
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0104
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B7603 : Block := .branch 176 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 52614058943912505055332653977786188707613571645456, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1689).pointIds 1689), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1693).pointIds 1693), (.leaf 5 (Common.fact 1694).pointIds 1694), (.leaf 6 (Common.fact 1695).pointIds 1695)]
theorem treeEq7603 : B7603.tree = HexagonCover.NBand.M8300_8500.SplitData.node7603 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7604 : Block := .branch 176 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17903395057303560747995139200774466990785173749776, 46773761428958395483787388422043726186730674847776, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1689).pointIds 1689), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1696).pointIds 1696), (.leaf 5 (Common.fact 1697).pointIds 1697), (.leaf 6 (Common.fact 1695).pointIds 1695)]
theorem treeEq7604 : B7604.tree = HexagonCover.NBand.M8300_8500.SplitData.node7604 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7602 : Block := .branch 165 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17903395057303560747995139200774466990785173749776, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B7603, B7604, (.leaf 0 [] 0)]
theorem treeEq7602 : B7602.tree = HexagonCover.NBand.M8300_8500.SplitData.node7602 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7603
  · exact treeEq7604
  · rfl

def B7605 : Block := .branch 176 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17540874143356246938206334564534295226143956107280, 365375452931403991296161839423942332109285621792, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1689).pointIds 1689), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1698).pointIds 1698), (.leaf 5 (Common.fact 1699).pointIds 1699), (.leaf 6 (Common.fact 1695).pointIds 1695)]
theorem treeEq7605 : B7605.tree = HexagonCover.NBand.M8300_8500.SplitData.node7605 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7601 : Block := .branch 158 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17540874143356246938206334564534295226143956107280, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), B7602, B7605, (.leaf 0 [] 0)]
theorem treeEq7601 : B7601.tree = HexagonCover.NBand.M8300_8500.SplitData.node7601 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7602
  · exact treeEq7605
  · rfl

def B7606 : Block := .branch 176 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538025223157134651100003376524964397961567109136, 5709034369502101269473775122669557740833472544, 14591635201607120147265351486411308567235653029855296] ![(.leaf 0 (Common.fact 1689).pointIds 1689), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1700).pointIds 1700), (.leaf 5 (Common.fact 1694).pointIds 1694), (.leaf 6 (Common.fact 1701).pointIds 1701)]
theorem treeEq7606 : B7606.tree = HexagonCover.NBand.M8300_8500.SplitData.node7606 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7600 : Block := .branch 151 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538025223157134651100003376524964397961567109136, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7601, (.leaf 5 (Common.fact 300).pointIds 300), B7606]
theorem treeEq7600 : B7600.tree = HexagonCover.NBand.M8300_8500.SplitData.node7600 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7601
  · rfl
  · exact treeEq7606

def B7607 : Block := .branch 176 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 14591632352686921034978245155223299236407470640857152] ![(.leaf 0 (Common.fact 1689).pointIds 1689), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1702).pointIds 1702), (.leaf 5 (Common.fact 1694).pointIds 1694), (.leaf 6 (Common.fact 1703).pointIds 1703)]
theorem treeEq7607 : B7607.tree = HexagonCover.NBand.M8300_8500.SplitData.node7607 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7599 : Block := .branch 142 ![51923602410648390402257511457489281, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B7600, (.leaf 5 (Common.fact 286).pointIds 286), B7607]
theorem treeEq7599 : B7599.tree = HexagonCover.NBand.M8300_8500.SplitData.node7599 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7600
  · rfl
  · exact treeEq7607

def B7608 : Block := .branch 176 ![31154414976509079888135526140608897, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369543639644342053743697801711467233312, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1704).pointIds 1704), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1702).pointIds 1702), (.leaf 5 (Common.fact 1705).pointIds 1705), (.leaf 6 (Common.fact 1695).pointIds 1695)]
theorem treeEq7608 : B7608.tree = HexagonCover.NBand.M8300_8500.SplitData.node7608 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7598 : Block := .branch 115 ![31154414976509079888135526140608897, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![B7599, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B7608, (.leaf 0 [] 0)]
theorem treeEq7598 : B7598.tree = HexagonCover.NBand.M8300_8500.SplitData.node7598 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7599
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7608
  · rfl

def B7609 : Block := .branch 176 ![10385227542369769374013540823728513, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034326987574591790606500261853797179326496, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1706).pointIds 1706), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1702).pointIds 1702), (.leaf 5 (Common.fact 1707).pointIds 1707), (.leaf 6 (Common.fact 1695).pointIds 1695)]
theorem treeEq7609 : B7609.tree = HexagonCover.NBand.M8300_8500.SplitData.node7609 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7597 : Block := .branch 114 ![10385227542369769374013540823728513, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![B7598, (.leaf 1 (Common.fact 1684).pointIds 1684), (.leaf 2 (Common.fact 1685).pointIds 1685), (.leaf 3 (Common.fact 1686).pointIds 1686), (.leaf 4 (Common.fact 1687).pointIds 1687), B7609, (.leaf 6 (Common.fact 1688).pointIds 1688)]
theorem treeEq7597 : B7597.tree = HexagonCover.NBand.M8300_8500.SplitData.node7597 := by
  change Tree.branch (114 : Fin 177) _ = Tree.branch (114 : Fin 177) _
  apply congrArg (Tree.branch (114 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7598
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7609
  · rfl

def B7610 : Block := .branch 176 ![633825300114116952548165288321, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248157579355386132605919349171706921024] ![(.leaf 0 (Common.fact 1708).pointIds 1708), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1702).pointIds 1702), (.leaf 5 (Common.fact 1694).pointIds 1694), (.leaf 6 (Common.fact 1709).pointIds 1709)]
theorem treeEq7610 : B7610.tree = HexagonCover.NBand.M8300_8500.SplitData.node7610 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7596 : Block := .branch 113 ![633825300114116952548165288321, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![B7597, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B7610]
theorem treeEq7596 : B7596.tree = HexagonCover.NBand.M8300_8500.SplitData.node7596 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7597
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7610

def B7611 : Block := .branch 176 ![618970019644941937263247745, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147195395494363064776988927400083520] ![(.leaf 0 (Common.fact 1710).pointIds 1710), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1691).pointIds 1691), (.leaf 3 (Common.fact 1692).pointIds 1692), (.leaf 4 (Common.fact 1702).pointIds 1702), (.leaf 5 (Common.fact 1694).pointIds 1694), (.leaf 6 (Common.fact 1711).pointIds 1711)]
theorem treeEq7611 : B7611.tree = HexagonCover.NBand.M8300_8500.SplitData.node7611 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7595 : Block := .branch 99 ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344675818414443492783249430532, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![B7596, (.leaf 1 (Common.fact 1592).pointIds 1592), (.leaf 2 (Common.fact 321).pointIds 321), (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), B7611]
theorem treeEq7595 : B7595.tree = HexagonCover.NBand.M8300_8500.SplitData.node7595 := by
  change Tree.branch (99 : Fin 177) _ = Tree.branch (99 : Fin 177) _
  apply congrArg (Tree.branch (99 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7596
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7611

def B7612 : Block := .branch 176 ![618970019644941937263247745, 2993155353253689176481146537402947660284146866980354, 47890485652059026823698344598447161988156516068235268, 89551429937849850547586381479748734728298504, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173141248147194761669062950662288179048480832] ![(.leaf 0 (Common.fact 1710).pointIds 1710), (.leaf 1 (Common.fact 1690).pointIds 1690), (.leaf 2 (Common.fact 1712).pointIds 1712), (.leaf 3 (Common.fact 1713).pointIds 1713), (.leaf 4 (Common.fact 1702).pointIds 1702), (.leaf 5 (Common.fact 1694).pointIds 1694), (.leaf 6 (Common.fact 1695).pointIds 1695)]
theorem treeEq7612 : B7612.tree = HexagonCover.NBand.M8300_8500.SplitData.node7612 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7594 : Block := .branch 86 ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344598447161988156516068235268, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034369502101269473775122669557740833472544, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B7595, B7612, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1590).pointIds 1590)]
theorem treeEq7594 : B7594.tree = HexagonCover.NBand.M8300_8500.SplitData.node7594 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7595
  · exact treeEq7612
  · rfl
  · rfl
  · rfl

def B7593 : Block := .branch 125 ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344598447161988156516068235268, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034326966805404356467189747731811862446112, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B7594, (.leaf 6 (Common.fact 1683).pointIds 1683)]
theorem treeEq7593 : B7593.tree = HexagonCover.NBand.M8300_8500.SplitData.node7593 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7594
  · rfl

theorem accepted7593 : B7593.accepted = true := by decide +kernel
theorem checked7593 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7593 (maskNeeds ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344598447161988156516068235268, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034326966805404356467189747731811862446112, 38536875173163031535589684870388098252392053335392320]) := by
  rw [← treeEq7593]
  exact B7593.sound accepted7593
#print axioms checked7593

def Tip7576_7593 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7593 ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344598447161988156516068235268, 89551429937849850528243568365914667932999688, 17538019653415352889179233408009389954779481997328, 5709034326966805404356467189747731811862446112, 38536875173163031535589684870388098252392053335392320] checked7593
def B7592 : Block := .branch 132 ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344598447161988156516068235268, 89551429937849850528243568365914667932999688, 17538019647970835018444217992595396235871190614032, 5709034326966805404356467189747731811862446112, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), Tip7576_7593, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 1603).pointIds 1603)]
theorem treeEq7592 : B7592.tree = HexagonCover.NBand.M8300_8500.SplitData.node7592 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7591 : Block := .branch 163 ![618970019644941937263247745, 2994616854891020079399350222235663943303802799523330, 47890485652059026823698344598447161988156516068235268, 89551429937849850528243568365914667932999688, 5846006549323611672814739330865132078623730270224, 5709034326966805404356467189747731811862446112, 38536875173163031535589684870388098252392053335392320] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B7592, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1682).pointIds 1682)]
theorem treeEq7591 : B7591.tree = HexagonCover.NBand.M8300_8500.SplitData.node7591 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7592
  · rfl
  · rfl

def B7590 : Block := .branch 169 ![618970019644941937263247745, 2994616854891020079399350222235664087418990875379202, 47890485652059026823698344598451893596025821077706756, 89551429937849929756406082630252261476950024, 5846007246221899126896712503856328098885027332112, 5709034326966805404356467189747731811862446112, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), (.leaf 5 (Common.fact 1681).pointIds 1681), B7591]
theorem treeEq7590 : B7590.tree = HexagonCover.NBand.M8300_8500.SplitData.node7590 := by
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
  · exact treeEq7591

def B7589 : Block := .branch 135 ![618970019644941937263247745, 2994616854891020079399350222235664087418990875379202, 47890485652059026823698344598451893596025821077706756, 89551429937849929756406082630252261476950024, 5846007246221899126896712503856328098885027332112, 5708990770823839524233143877797980545531379744, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B7590, (.leaf 6 (Common.fact 1680).pointIds 1680)]
theorem treeEq7589 : B7589.tree = HexagonCover.NBand.M8300_8500.SplitData.node7589 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7590
  · rfl

def B7588 : Block := .branch 144 ![618970019644941937263247745, 2994616854891020079399350222235664087418990875379202, 47890485652059026823698344598451893596025821077706756, 89551429937849929756406082630252261476950024, 5846007246221899126896712503856328098885027332112, 5708990770823839524233143877797980545531379744, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B7589, (.leaf 6 (Common.fact 1679).pointIds 1679)]
theorem treeEq7588 : B7588.tree = HexagonCover.NBand.M8300_8500.SplitData.node7588 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7589
  · rfl

def B7587 : Block := .branch 152 ![618970019644941937263247745, 2994616854891020079399350222235664087418990875379202, 47890485652059026823698344598451893596025821077706756, 89551429937849929756406082630252261476950024, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 1264).pointIds 1264), B7588, (.leaf 6 (Common.fact 1678).pointIds 1678)]
theorem treeEq7587 : B7587.tree = HexagonCover.NBand.M8300_8500.SplitData.node7587 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7588
  · rfl

def B7586 : Block := .branch 171 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 89551429937849929756406082630252261476950024, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 1008).pointIds 1008), B7587, (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 1677).pointIds 1677)]
theorem treeEq7586 : B7586.tree = HexagonCover.NBand.M8300_8500.SplitData.node7586 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7587
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7585 : Block := .branch 98 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 89551429937849612843756025572901887301148680, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B7586, (.leaf 4 (Common.fact 1676).pointIds 1676), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 1591).pointIds 1591)]
theorem treeEq7585 : B7585.tree = HexagonCover.NBand.M8300_8500.SplitData.node7585 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7586
  · rfl
  · rfl
  · rfl

def B7584 : Block := .branch 108 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 89551429937849612843756025572901887301148680, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B7585, (.leaf 4 (Common.fact 1675).pointIds 1675), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 1593).pointIds 1593)]
theorem treeEq7584 : B7584.tree = HexagonCover.NBand.M8300_8500.SplitData.node7584 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7585
  · rfl
  · rfl
  · rfl

def B7583 : Block := .branch 119 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 89551429937849612843756025572901887301148680, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B7584, (.leaf 4 (Common.fact 1674).pointIds 1674), (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1594).pointIds 1594)]
theorem treeEq7583 : B7583.tree = HexagonCover.NBand.M8300_8500.SplitData.node7583 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7584
  · rfl
  · rfl
  · rfl

def B7582 : Block := .branch 129 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 89551429937849612843756025572901887301148680, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), B7583, (.leaf 4 (Common.fact 1673).pointIds 1673), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1597).pointIds 1597)]
theorem treeEq7582 : B7582.tree = HexagonCover.NBand.M8300_8500.SplitData.node7582 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7583
  · rfl
  · rfl
  · rfl

def B7581 : Block := .branch 138 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 89202980794122571857169529974891756652617736, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), B7582, (.leaf 4 (Common.fact 1672).pointIds 1672), (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1605).pointIds 1605)]
theorem treeEq7581 : B7581.tree = HexagonCover.NBand.M8300_8500.SplitData.node7581 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7582
  · rfl
  · rfl
  · rfl

def B7580 : Block := .branch 146 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 79291026656884298310628696072, 5846007246221899126896712503856328098885027332112, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), B7581, (.leaf 4 (Common.fact 1671).pointIds 1671), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7580 : B7580.tree = HexagonCover.NBand.M8300_8500.SplitData.node7580 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7581
  · rfl
  · rfl
  · rfl

def B7579 : Block := .branch 162 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 237747351685412973497716596744, 696898287454081973172991196020261297160208, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1670).pointIds 1670), B7580, (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 1609).pointIds 1609)]
theorem treeEq7579 : B7579.tree = HexagonCover.NBand.M8300_8500.SplitData.node7579 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7580
  · rfl
  · rfl

def B7578 : Block := .branch 85 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 47890485652059026823698344598451893596025821077706756, 237708666059185305364125999112, 696898287454081973172991196020261297160208, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 1669).pointIds 1669), B7579, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7578 : B7578.tree = HexagonCover.NBand.M8300_8500.SplitData.node7578 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7579
  · rfl
  · rfl
  · rfl

def B7577 : Block := .branch 175 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4731607940223509469188, 237708666059185305364125999112, 696899616682077758088864099827321577504784, 393248, 37788586334849609241469398236037361346328215873388608] ![(.leaf 0 (Common.fact 1654).pointIds 1654), (.leaf 1 (Common.fact 1638).pointIds 1638), B7578, (.leaf 3 (Common.fact 1664).pointIds 1664), (.leaf 4 (Common.fact 1656).pointIds 1656), (.leaf 5 (Common.fact 1646).pointIds 1646), (.leaf 6 (Common.fact 1643).pointIds 1643)]
theorem treeEq7577 : B7577.tree = HexagonCover.NBand.M8300_8500.SplitData.node7577 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7578
  · rfl
  · rfl
  · rfl
  · rfl

def B7576 : Block := .branch 170 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4731607940223509469188, 237708666059185305364125999112, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7577]
theorem treeEq7576 : B7576.tree = HexagonCover.NBand.M8300_8500.SplitData.node7576 := by
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
  · exact treeEq7577

theorem accepted7576 : B7576.accepted = true := by decide +kernel
theorem checked7576 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7576 (maskNeeds ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4731607940223509469188, 237708666059185305364125999112, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184]) := by
  rw [← treeEq7576]
  exact B7576.sound accepted7576
#print axioms checked7576

def B7565 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 795422266117343913232355470205837033447741286907936, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 1242).pointIds 1242), (.leaf 6 (Common.fact 1644).pointIds 1644)]
theorem treeEq7565 : B7565.tree = HexagonCover.NBand.M8300_8500.SplitData.node7565 := by
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

def B7564 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 47133427803921619112068835855100127383903824904224, 84182497164755393500452008481029840831172536996200512] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7565, (.leaf 6 (Common.fact 1667).pointIds 1667)]
theorem treeEq7564 : B7564.tree = HexagonCover.NBand.M8300_8500.SplitData.node7564 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7565
  · rfl

def B7563 : Block := .branch 151 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 11692102999206869656045894904521299985818317848592, 47133427803921619112068835855100127383903824904224, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), B7564]
theorem treeEq7563 : B7563.tree = HexagonCover.NBand.M8300_8500.SplitData.node7563 := by
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
  · exact treeEq7564

def B7562 : Block := .branch 158 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 11692102999206869656045894904521299985818317848592, 46768052394588893382517914646921056628989841768480, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), (.leaf 4 (Common.fact 1666).pointIds 1666), B7563, (.leaf 0 [] 0)]
theorem treeEq7562 : B7562.tree = HexagonCover.NBand.M8300_8500.SplitData.node7562 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7563
  · rfl

def B7561 : Block := .branch 163 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 89900559646310416416242791035828570857504784, 46768052394588893382517914646921056628989841768480, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B7562, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1665).pointIds 1665)]
theorem treeEq7561 : B7561.tree = HexagonCover.NBand.M8300_8500.SplitData.node7561 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7562
  · rfl
  · rfl

def B7560 : Block := .branch 86 ![385, 144115188075857410, 4731607869854765291524, 1496577676626844588240652501699691354923785166807048, 89900559646310416416242791035828570857504784, 46768052394588893382517914646921056628989841768480, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B7561, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1590).pointIds 1590)]
theorem treeEq7560 : B7560.tree = HexagonCover.NBand.M8300_8500.SplitData.node7560 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7561
  · rfl
  · rfl
  · rfl
  · rfl

def B7559 : Block := .branch 129 ![385, 144115188075857410, 4731607869854765291524, 1496577676626844588240652501699691354923785166807048, 89899879081576574539315864286613707321081872, 46768052394588893382517914646921056628989841768480, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B7560, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1597).pointIds 1597)]
theorem treeEq7559 : B7559.tree = HexagonCover.NBand.M8300_8500.SplitData.node7559 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7560
  · rfl
  · rfl

def B7558 : Block := .branch 138 ![385, 144115188075857410, 4731607869854765291524, 1496577676626844588240652501699691354923785166807048, 89899879081576574539315864286613707321081872, 46768052394588893382517914646921056628989841768480, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B7559, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1605).pointIds 1605)]
theorem treeEq7558 : B7558.tree = HexagonCover.NBand.M8300_8500.SplitData.node7558 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7559
  · rfl
  · rfl

def B7557 : Block := .branch 165 ![385, 144115188075857410, 4731607869854765291524, 1496577676626844588240652501699691354923785166807048, 89899880410804570324231737190420767601426448, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 760).pointIds 760), B7558, (.leaf 0 [] 0)]
theorem treeEq7557 : B7557.tree = HexagonCover.NBand.M8300_8500.SplitData.node7557 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7558
  · rfl

def B7556 : Block := .branch 167 ![385, 144115188075857410, 4731607869854765291524, 1496577676626844588240652501699691354923785166807048, 89899880410804570324231737190420767601426448, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 759).pointIds 759), B7557, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7556 : B7556.tree = HexagonCover.NBand.M8300_8500.SplitData.node7556 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7557
  · rfl

def B7555 : Block := .branch 146 ![385, 144115188075857410, 4731607869854765291524, 1496577676626844588240652501699691354923785166807048, 696899616682077758088864099827321577504784, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B7556, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7555 : B7555.tree = HexagonCover.NBand.M8300_8500.SplitData.node7555 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7556
  · rfl
  · rfl

def B7554 : Block := .branch 170 ![385, 144115188075857410, 4731607869854765291524, 79232998217542796110242799624, 696899616682077758088864099827321577504784, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7555, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1643).pointIds 1643)]
theorem treeEq7554 : B7554.tree = HexagonCover.NBand.M8300_8500.SplitData.node7554 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7555
  · rfl
  · rfl
  · rfl

def B7553 : Block := .branch 175 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 9713917096720214068828164, 237689323246071471297330700296, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 1654).pointIds 1654), (.leaf 1 (Common.fact 1638).pointIds 1638), (.leaf 2 (Common.fact 1663).pointIds 1663), (.leaf 3 (Common.fact 1664).pointIds 1664), (.leaf 4 (Common.fact 1656).pointIds 1656), (.leaf 5 (Common.fact 1646).pointIds 1646), B7554]
theorem treeEq7553 : B7553.tree = HexagonCover.NBand.M8300_8500.SplitData.node7553 := by
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
  · exact treeEq7554

theorem accepted7553 : B7553.accepted = true := by decide +kernel
theorem checked7553 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7553 (maskNeeds ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 9713917096720214068828164, 237689323246071471297330700296, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184]) := by
  rw [← treeEq7553]
  exact B7553.sound accepted7553
#print axioms checked7553

def Tip7459_7463 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7463 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 130606499058183131539445764, 79228162514264337593543974920, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] HexagonCover.NBand.M8300_8500.SplitTree.Run0103.checked7463
def B7538 : Block := .branch 161 ![385, 1538, 4873482210392392360531972, 77371252455336267181219848, 98320, 393248, 37788586334827825853074475034712213756224341586477120] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 687).pointIds 687), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1660).pointIds 1660)]
theorem treeEq7538 : B7538.tree = HexagonCover.NBand.M8300_8500.SplitData.node7538 := by
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

def B7537 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 77371252455336267181219848, 98320, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7538]
theorem treeEq7537 : B7537.tree = HexagonCover.NBand.M8300_8500.SplitData.node7537 := by
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
  · exact treeEq7538

def B7462 : Block := .branch 86 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 53235246602846864358250500, 79228162514264337593543974920, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), Tip7459_7463, B7537, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1590).pointIds 1590)]
theorem treeEq7462 : B7462.tree = HexagonCover.NBand.M8300_8500.SplitData.node7462 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7537
  · rfl
  · rfl
  · rfl

def B7540 : Block := .branch 161 ![385, 1538, 4873482210392392360531972, 158495010654756343320678522888, 98320, 393248, 37788586334827825853074475034712213756224341586477120] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 969).pointIds 969), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1660).pointIds 1660)]
theorem treeEq7540 : B7540.tree = HexagonCover.NBand.M8300_8500.SplitData.node7540 := by
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

def B7539 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 158495010654756343320678522888, 98320, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 968).pointIds 968), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7540]
theorem treeEq7539 : B7539.tree = HexagonCover.NBand.M8300_8500.SplitData.node7539 := by
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
  · exact treeEq7540

def B7461 : Block := .branch 85 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 14549620375178730767652868, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B7462, B7539, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7461 : B7461.tree = HexagonCover.NBand.M8300_8500.SplitData.node7461 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7462
  · exact treeEq7539
  · rfl
  · rfl
  · rfl

def B7542 : Block := .branch 161 ![385, 1538, 4873482210392392360531972, 158475667841642509253883224072, 98320, 393248, 37788586334827825853074475034712213756224341586477120] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 971).pointIds 971), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1660).pointIds 1660)]
theorem treeEq7542 : B7542.tree = HexagonCover.NBand.M8300_8500.SplitData.node7542 := by
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

def B7541 : Block := .branch 170 ![385, 144115188075857410, 4878213818261697370003460, 158475667841642509253883224072, 98320, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7542]
theorem treeEq7541 : B7541.tree = HexagonCover.NBand.M8300_8500.SplitData.node7541 := by
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
  · exact treeEq7542

def B7460 : Block := .branch 84 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 14549620375178730767652868, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B7461, B7541, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7460 : B7460.tree = HexagonCover.NBand.M8300_8500.SplitData.node7460 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7461
  · exact treeEq7541
  · rfl
  · rfl
  · rfl

def B7551 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202982787964486243516682446304036444536848, 393248, 36294931661475643070670309135676172510135978527555648] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1661).pointIds 1661), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1662).pointIds 1662)]
theorem treeEq7551 : B7551.tree = HexagonCover.NBand.M8300_8500.SplitData.node7551 := by
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

def B7550 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202982123350488351058745994400506304364560, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B7551, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1594).pointIds 1594)]
theorem treeEq7550 : B7550.tree = HexagonCover.NBand.M8300_8500.SplitData.node7550 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7551
  · rfl
  · rfl

def B7549 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202982123350488351058745994400506304364560, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B7550, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1597).pointIds 1597)]
theorem treeEq7549 : B7549.tree = HexagonCover.NBand.M8300_8500.SplitData.node7549 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7550
  · rfl
  · rfl

def B7548 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202982123350488351058745994400506304364560, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B7549, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1605).pointIds 1605)]
theorem treeEq7548 : B7548.tree = HexagonCover.NBand.M8300_8500.SplitData.node7548 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7549
  · rfl
  · rfl

def B7547 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202982123350488351058745994400506304364560, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 760).pointIds 760), B7548, (.leaf 0 [] 0)]
theorem treeEq7547 : B7547.tree = HexagonCover.NBand.M8300_8500.SplitData.node7547 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7548
  · rfl

def B7546 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202982123350488351058745994400506304364560, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 759).pointIds 759), B7547, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7546 : B7546.tree = HexagonCover.NBand.M8300_8500.SplitData.node7546 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7547
  · rfl

def B7545 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 1329227995784915872903807060280442896, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B7546, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7545 : B7545.tree = HexagonCover.NBand.M8300_8500.SplitData.node7545 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7546
  · rfl
  · rfl

def B7544 : Block := .branch 170 ![385, 144115188075857410, 4731607869854765291524, 9671406556917033397673992, 1329227995784915872903807060280442896, 393248, 36294931661497426459065232337001320100239852814467136] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7545, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1660).pointIds 1660)]
theorem treeEq7544 : B7544.tree = HexagonCover.NBand.M8300_8500.SplitData.node7544 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7545
  · rfl
  · rfl
  · rfl

def B7543 : Block := .branch 161 ![385, 144115188075857410, 4878213818261697370003460, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1598).pointIds 1598), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7544]
theorem treeEq7543 : B7543.tree = HexagonCover.NBand.M8300_8500.SplitData.node7543 := by
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
  · exact treeEq7544

def B7459 : Block := .branch 83 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4878213818261697370003460, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B7460, B7543, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq7459 : B7459.tree = HexagonCover.NBand.M8300_8500.SplitData.node7459 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7460
  · exact treeEq7543
  · rfl
  · rfl
  · rfl

theorem accepted7459 : B7459.accepted = true := by decide +kernel
theorem checked7459 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7459 (maskNeeds ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4878213818261697370003460, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184]) := by
  rw [← treeEq7459]
  exact B7459.sound accepted7459
#print axioms checked7459

end HexagonCover.NBand.M8300_8500.SplitTree.Run0104
