import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0007
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0597_0598 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0598 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] HexagonCover.NBand.M8500_8700.SplitTree.Run0007.checked0598
def B0633 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M8500_8700.SplitData.node0633 := by
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
  · rfl

def B0632 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0633, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M8500_8700.SplitData.node0632 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0633
  · rfl
  · rfl

def B0631 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0632, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0631 : B0631.tree = HexagonCover.NBand.M8500_8700.SplitData.node0631 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0632
  · rfl
  · rfl

def B0630 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0631, (.leaf 0 [] 0)]
theorem treeEq0630 : B0630.tree = HexagonCover.NBand.M8500_8700.SplitData.node0630 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0631
  · rfl

def B0629 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0630, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M8500_8700.SplitData.node0629 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0630
  · rfl

def B0628 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0629, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M8500_8700.SplitData.node0628 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0629
  · rfl
  · rfl

def B0627 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 392).pointIds 392), B0628, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M8500_8700.SplitData.node0627 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0628
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0626 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0627, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M8500_8700.SplitData.node0626 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0627
  · rfl
  · rfl
  · rfl
  · rfl

def B0625 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0626, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M8500_8700.SplitData.node0625 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0626
  · rfl
  · rfl
  · rfl

def B0597 : Block := .branch 114 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![Tip0597_0598, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0625]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M8500_8700.SplitData.node0597 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0625

theorem accepted0597 : B0597.accepted = true := by decide +kernel
theorem checked0597 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0597 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq0597]
  exact B0597.sound accepted0597
#print axioms checked0597

def Tip0521_0560 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0560 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] HexagonCover.NBand.M8500_8700.SplitTree.Run0007.checked0560
def Tip0521_0522 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0522 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0007.checked0522
def B0595 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M8500_8700.SplitData.node0595 := by
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
  · rfl

def B0594 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0595, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M8500_8700.SplitData.node0594 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0595
  · rfl
  · rfl

def B0593 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0594, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M8500_8700.SplitData.node0593 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0594
  · rfl
  · rfl

def B0592 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0593, (.leaf 0 [] 0)]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M8500_8700.SplitData.node0592 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0593
  · rfl

def B0591 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0592, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M8500_8700.SplitData.node0591 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0592
  · rfl

def B0590 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0591, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M8500_8700.SplitData.node0590 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0591
  · rfl
  · rfl

def B0589 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638415905248055100553741398353533993024] ![(.leaf 0 (Common.fact 392).pointIds 392), B0590, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M8500_8700.SplitData.node0589 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0590
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0588 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 11226638415905248055100553741398353533993024] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0589, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M8500_8700.SplitData.node0588 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0589
  · rfl
  · rfl
  · rfl
  · rfl

def B0587 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 11226638415905248055100553741398353533993024] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0588, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M8500_8700.SplitData.node0587 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0588
  · rfl
  · rfl
  · rfl

def B0559 : Block := .branch 114 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] ![Tip0521_0560, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0587]
theorem treeEq0559 : B0559.tree = HexagonCover.NBand.M8500_8700.SplitData.node0559 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0587

def B0521 : Block := .branch 113 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip0521_0522, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0559]
theorem treeEq0521 : B0521.tree = HexagonCover.NBand.M8500_8700.SplitData.node0521 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0559

theorem accepted0521 : B0521.accepted = true := by decide +kernel
theorem checked0521 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0521 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0521]
  exact B0521.sound accepted0521
#print axioms checked0521

def Tip0519_0635 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0635 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] HexagonCover.NBand.M8500_8700.SplitTree.Run0007.checked0635
def Tip0519_0597 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0597 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] checked0597
def Tip0519_0521 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0521 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] checked0521
def B0670 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0670 : B0670.tree = HexagonCover.NBand.M8500_8700.SplitData.node0670 := by
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
  · rfl

def B0669 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0670, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0669 : B0669.tree = HexagonCover.NBand.M8500_8700.SplitData.node0669 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0670
  · rfl
  · rfl

def B0668 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0669, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M8500_8700.SplitData.node0668 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0669
  · rfl
  · rfl

def B0667 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0668, (.leaf 0 [] 0)]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M8500_8700.SplitData.node0667 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0668
  · rfl

def B0666 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0667, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M8500_8700.SplitData.node0666 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0667
  · rfl

def B0665 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0666, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M8500_8700.SplitData.node0665 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0666
  · rfl
  · rfl

def B0664 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638415905248055100553741398353533993024] ![(.leaf 0 (Common.fact 392).pointIds 392), B0665, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M8500_8700.SplitData.node0664 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0665
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0663 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 11226638415905248055100553741398353533993024] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0664, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M8500_8700.SplitData.node0663 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0664
  · rfl
  · rfl
  · rfl
  · rfl

def B0662 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 11226638415905248055100553741398353533993024] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0663, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M8500_8700.SplitData.node0662 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0663
  · rfl
  · rfl
  · rfl

def B0634 : Block := .branch 114 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] ![Tip0519_0635, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0662]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M8500_8700.SplitData.node0634 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0662

def B0596 : Block := .branch 113 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![Tip0519_0597, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B0634]
theorem treeEq0596 : B0596.tree = HexagonCover.NBand.M8500_8700.SplitData.node0596 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0634

def B0520 : Block := .branch 112 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip0519_0521, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B0596]
theorem treeEq0520 : B0520.tree = HexagonCover.NBand.M8500_8700.SplitData.node0520 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0596

def B0672 : Block := .branch 168 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 761).pointIds 761), (.leaf 1 (Common.fact 767).pointIds 767), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M8500_8700.SplitData.node0672 := by
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

def B0671 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0672, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M8500_8700.SplitData.node0671 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0672
  · rfl

def B0519 : Block := .branch 109 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B0520, (.leaf 5 (Common.fact 294).pointIds 294), B0671]
theorem treeEq0519 : B0519.tree = HexagonCover.NBand.M8500_8700.SplitData.node0519 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0520
  · rfl
  · exact treeEq0671

theorem accepted0519 : B0519.accepted = true := by decide +kernel
theorem checked0519 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0519 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0519]
  exact B0519.sound accepted0519
#print axioms checked0519

def Tip0517_0519 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0519 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] checked0519
def B0677 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0677 : B0677.tree = HexagonCover.NBand.M8500_8700.SplitData.node0677 := by
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

def B0676 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0677, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0676 : B0676.tree = HexagonCover.NBand.M8500_8700.SplitData.node0676 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0677
  · rfl

def B0675 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B0676]
theorem treeEq0675 : B0675.tree = HexagonCover.NBand.M8500_8700.SplitData.node0675 := by
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
  · exact treeEq0676

def B0674 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B0675, (.leaf 0 [] 0)]
theorem treeEq0674 : B0674.tree = HexagonCover.NBand.M8500_8700.SplitData.node0674 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0675
  · rfl

def B0673 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B0674, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0673 : B0673.tree = HexagonCover.NBand.M8500_8700.SplitData.node0673 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0674
  · rfl

def B0518 : Block := .branch 108 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip0517_0519, B0673, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq0518 : B0518.tree = HexagonCover.NBand.M8500_8700.SplitData.node0518 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0673
  · rfl
  · rfl

def B0686 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203662688084330227985672743615369840787472, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 846).pointIds 846), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq0686 : B0686.tree = HexagonCover.NBand.M8500_8700.SplitData.node0686 := by
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
  · rfl

def B0685 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202982123350488351058745994400506304364560, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0686, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0685 : B0685.tree = HexagonCover.NBand.M8500_8700.SplitData.node0685 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0686
  · rfl
  · rfl

def B0684 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202982123350488351058745994400506304364560, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0685, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0684 : B0684.tree = HexagonCover.NBand.M8500_8700.SplitData.node0684 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0685
  · rfl
  · rfl

def B0683 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202982123350488351058745994400506304364560, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 845).pointIds 845), B0684, (.leaf 0 [] 0)]
theorem treeEq0683 : B0683.tree = HexagonCover.NBand.M8500_8700.SplitData.node0683 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0684
  · rfl

def B0682 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202982123350488351058745994400506304364560, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 844).pointIds 844), B0683, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0682 : B0682.tree = HexagonCover.NBand.M8500_8700.SplitData.node0682 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0683
  · rfl

def B0681 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0682, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0681 : B0681.tree = HexagonCover.NBand.M8500_8700.SplitData.node0681 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0682
  · rfl
  · rfl

def B0680 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 392).pointIds 392), B0681, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0680 : B0680.tree = HexagonCover.NBand.M8500_8700.SplitData.node0680 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0681
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0679 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0680, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0679 : B0679.tree = HexagonCover.NBand.M8500_8700.SplitData.node0679 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0680
  · rfl
  · rfl
  · rfl
  · rfl

def B0678 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 11226638384752734554491816199616872261877824] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0679, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0678 : B0678.tree = HexagonCover.NBand.M8500_8700.SplitData.node0678 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0679
  · rfl
  · rfl
  · rfl

def B0517 : Block := .branch 100 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B0518, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B0678]
theorem treeEq0517 : B0517.tree = HexagonCover.NBand.M8500_8700.SplitData.node0517 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0518
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0678

theorem accepted0517 : B0517.accepted = true := by decide +kernel
theorem checked0517 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0517 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 554601973303128821671506501640, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0517]
  exact B0517.sound accepted0517
#print axioms checked0517

def B0705 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M8500_8700.SplitData.node0705 := by
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

def B0704 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0705, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M8500_8700.SplitData.node0704 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0705
  · rfl

def B0703 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0704]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M8500_8700.SplitData.node0703 := by
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
  · exact treeEq0704

def B0710 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M8500_8700.SplitData.node0710 := by
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

def B0709 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0710, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M8500_8700.SplitData.node0709 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0710
  · rfl

def B0708 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0709]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M8500_8700.SplitData.node0708 := by
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
  · exact treeEq0709

def B0707 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0708, (.leaf 0 [] 0)]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M8500_8700.SplitData.node0707 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0708
  · rfl

def B0706 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0707, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M8500_8700.SplitData.node0706 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0707
  · rfl

def B0702 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0703, B0706, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M8500_8700.SplitData.node0702 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0703
  · exact treeEq0706
  · rfl
  · rfl

def B0715 : Block := .branch 160 ![385, 928455029464035755930158594, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M8500_8700.SplitData.node0715 := by
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
  · rfl

def B0714 : Block := .branch 172 ![1238242271318996484309909889, 928681703055213498900416002, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0715, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M8500_8700.SplitData.node0714 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0715
  · rfl
  · rfl
  · rfl
  · rfl

def B0713 : Block := .branch 171 ![1238242271318996484309909889, 928681703055213498900416002, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0714, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M8500_8700.SplitData.node0713 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0714
  · rfl
  · rfl
  · rfl

def B0712 : Block := .branch 169 ![1238242271318996484309909889, 928681703055213498900416002, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0713]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M8500_8700.SplitData.node0712 := by
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
  · exact treeEq0713

def B0711 : Block := .branch 170 ![1238242271318996484309909889, 928681703055213498900416002, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0712, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M8500_8700.SplitData.node0711 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0712
  · rfl

def B0701 : Block := .branch 121 ![1238242271318996484309909889, 928681703055213498900416002, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0702, (.leaf 5 (Common.fact 319).pointIds 319), B0711]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M8500_8700.SplitData.node0701 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0702
  · rfl
  · exact treeEq0711

theorem accepted0701 : B0701.accepted = true := by decide +kernel
theorem checked0701 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0701 (maskNeeds ![1238242271318996484309909889, 928681703055213498900416002, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq0701]
  exact B0701.sound accepted0701
#print axioms checked0701

end HexagonCover.NBand.M8500_8700.SplitTree.Run0008
