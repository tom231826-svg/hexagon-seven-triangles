import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0018
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0019
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1469_1471 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1471 ![590295810358705652097, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7500_7700.SplitTree.Run0018.checked1471
def B1498 : Block := .branch 132 ![385, 1538, 6148, 24584, 5986493394212044715827068535409984783888156687695888, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 919).pointIds 919), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1498 : B1498.tree = HexagonCover.NBand.M7500_7700.SplitData.node1498 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1497 : Block := .branch 157 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2865645758011185073687339798035314453518876704, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1498, (.leaf 5 (Common.fact 918).pointIds 918), (.leaf 0 [] 0)]
theorem treeEq1497 : B1497.tree = HexagonCover.NBand.M7500_7700.SplitData.node1497 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1498
  · rfl
  · rfl

def B1496 : Block := .branch 143 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 916).pointIds 916), B1497, (.leaf 6 (Common.fact 917).pointIds 917)]
theorem treeEq1496 : B1496.tree = HexagonCover.NBand.M7500_7700.SplitData.node1496 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1497
  · rfl

def B1495 : Block := .branch 125 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 21778071483257438539818060054518889447488] ![B1496, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq1495 : B1495.tree = HexagonCover.NBand.M7500_7700.SplitData.node1495 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1496
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1494 : Block := .branch 151 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257438539818060054518889447488] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1495, (.leaf 6 (Common.fact 914).pointIds 914)]
theorem treeEq1494 : B1494.tree = HexagonCover.NBand.M7500_7700.SplitData.node1494 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1495
  · rfl

def B1493 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 21778071483257438539818060054518889447488] ![B1494, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1493 : B1493.tree = HexagonCover.NBand.M7500_7700.SplitData.node1493 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1494
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1492 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257438539818060054518889447488] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1493, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1492 : B1492.tree = HexagonCover.NBand.M7500_7700.SplitData.node1492 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1493
  · rfl

def B1491 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257438539818060054518889447488] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1492, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 912).pointIds 912)]
theorem treeEq1491 : B1491.tree = HexagonCover.NBand.M7500_7700.SplitData.node1491 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1492
  · rfl
  · rfl

def B1470 : Block := .branch 69 ![385, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1469_1471, (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), B1491]
theorem treeEq1470 : B1470.tree = HexagonCover.NBand.M7500_7700.SplitData.node1470 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1491

def B1507 : Block := .branch 160 ![385, 374144419156711147060143317477599907935576024679938, 18446884811197913092, 24584, 98320, 393248, 5596964371117181184008395383152815988277312] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 883).pointIds 883), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq1507 : B1507.tree = HexagonCover.NBand.M7500_7700.SplitData.node1507 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1506 : Block := .branch 168 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 5596964371117181184008395383152815988277312] ![(.leaf 0 (Common.fact 944).pointIds 944), B1507, (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq1506 : B1506.tree = HexagonCover.NBand.M7500_7700.SplitData.node1506 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1507
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1505 : Block := .branch 142 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 5986310709643420646505661954084355630601875532906512, 393248, 21778071484525398624465814990725611782208] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), (.leaf 4 (Common.fact 943).pointIds 943), (.leaf 5 (Common.fact 152).pointIds 152), B1506]
theorem treeEq1505 : B1505.tree = HexagonCover.NBand.M7500_7700.SplitData.node1505 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1506

def B1504 : Block := .branch 138 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 79266848140492005727134572552, 5986310709294971502778620967497860032591744884375568, 393248, 21778071484525398624465814990725611782208] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B1505, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1504 : B1504.tree = HexagonCover.NBand.M7500_7700.SplitData.node1504 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1505
  · rfl
  · rfl

def B1503 : Block := .branch 141 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 79266848140492005727134572552, 5986310706507378352962293074805895248510699696128016, 393248, 21778071484525398624465814990725611782208] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), B1504, (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1503 : B1503.tree = HexagonCover.NBand.M7500_7700.SplitData.node1503 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1504
  · rfl
  · rfl

def B1502 : Block := .branch 100 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 79266848140492005727134572552, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1503]
theorem treeEq1502 : B1502.tree = HexagonCover.NBand.M7500_7700.SplitData.node1502 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1503

def B1501 : Block := .branch 170 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 21778071483258057509247406934297633357888] ![B1502, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1501 : B1501.tree = HexagonCover.NBand.M7500_7700.SplitData.node1501 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1502
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1500 : Block := .branch 171 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1501, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1500 : B1500.tree = HexagonCover.NBand.M7500_7700.SplitData.node1500 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1501
  · rfl

def B1499 : Block := .branch 172 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1500, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq1499 : B1499.tree = HexagonCover.NBand.M7500_7700.SplitData.node1499 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1500
  · rfl
  · rfl

def B1469 : Block := .branch 89 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 70).pointIds 70), B1470, (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), (.leaf 4 (Common.fact 74).pointIds 74), (.leaf 5 (Common.fact 75).pointIds 75), B1499]
theorem treeEq1469 : B1469.tree = HexagonCover.NBand.M7500_7700.SplitData.node1469 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1470
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1499

theorem accepted1469 : B1469.accepted = true := by decide +kernel
theorem checked1469 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1469 (maskNeeds ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1469]
  exact B1469.sound accepted1469
#print axioms checked1469

def Tip1468_1469 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1469 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1469
def B1517 : Block := .branch 160 ![385, 374144419156711147060143317477599907935576024679938, 18446884811197913092, 24584, 98320, 393248, 5596964371116863884502076049121105906499648] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 883).pointIds 883), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq1517 : B1517.tree = HexagonCover.NBand.M7500_7700.SplitData.node1517 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1516 : Block := .branch 168 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 5596964371116863884502076049121105906499648] ![(.leaf 0 (Common.fact 944).pointIds 944), B1517, (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq1516 : B1516.tree = HexagonCover.NBand.M7500_7700.SplitData.node1516 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1517
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1515 : Block := .branch 142 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 11692013098647223345629478661730264157247460442128, 393248, 21778071484208099118146480959015530004544] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), (.leaf 4 (Common.fact 951).pointIds 951), (.leaf 5 (Common.fact 152).pointIds 152), B1516]
theorem treeEq1515 : B1515.tree = HexagonCover.NBand.M7500_7700.SplitData.node1515 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1516

def B1514 : Block := .branch 163 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 32667107225995042599031525747206288572480] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1515, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 950).pointIds 950)]
theorem treeEq1514 : B1514.tree = HexagonCover.NBand.M7500_7700.SplitData.node1514 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1515
  · rfl
  · rfl

def B1513 : Block := .branch 133 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 2722258935367507707706996859454145789968, 393248, 21778071484525011768203538309389705805888] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 949).pointIds 949), (.leaf 5 (Common.fact 198).pointIds 198), B1514]
theorem treeEq1513 : B1513.tree = HexagonCover.NBand.M7500_7700.SplitData.node1513 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1514

def B1512 : Block := .branch 131 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071484525011768203538309389705805888] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B1513, (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq1512 : B1512.tree = HexagonCover.NBand.M7500_7700.SplitData.node1512 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1513
  · rfl
  · rfl

def B1511 : Block := .branch 100 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1512]
theorem treeEq1511 : B1511.tree = HexagonCover.NBand.M7500_7700.SplitData.node1511 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1512

def B1510 : Block := .branch 170 ![385, 302231599018845369533954, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 21778071483257515910480219580427364991040] ![B1511, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1510 : B1510.tree = HexagonCover.NBand.M7500_7700.SplitData.node1510 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1511
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1509 : Block := .branch 171 ![385, 302231599018845369533954, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1510, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1509 : B1509.tree = HexagonCover.NBand.M7500_7700.SplitData.node1509 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1510
  · rfl

def B1508 : Block := .branch 172 ![385, 302231599018845369533954, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1509, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq1508 : B1508.tree = HexagonCover.NBand.M7500_7700.SplitData.node1508 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1509
  · rfl
  · rfl

def B1468 : Block := .branch 86 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 891).pointIds 891), Tip1468_1469, (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), B1508]
theorem treeEq1468 : B1468.tree = HexagonCover.NBand.M7500_7700.SplitData.node1468 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1508

theorem accepted1468 : B1468.accepted = true := by decide +kernel
theorem checked1468 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1468 (maskNeeds ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1468]
  exact B1468.sound accepted1468
#print axioms checked1468

def B1545 : Block := .branch 124 ![5193564509135055857931993032425857, 1538, 6148, 24584, 98320, 393248, 5986310717679529023710861619961025280787351869063232] ![(.leaf 0 (Common.fact 973).pointIds 973), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq1545 : B1545.tree = HexagonCover.NBand.M7500_7700.SplitData.node1545 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1544 : Block := .branch 143 ![5193564509135055857931993032425857, 1538, 6148, 24584, 2993340895453740951265684114578976058623079605174288, 42535295865117307932921825928971419680, 5986310706529156424445550049193166144463171116073024] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 972).pointIds 972), (.leaf 5 (Common.fact 569).pointIds 569), B1545]
theorem treeEq1544 : B1544.tree = HexagonCover.NBand.M7500_7700.SplitData.node1544 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1545

def B1543 : Block := .branch 171 ![5193564509135055857931993032425857, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 1496577676626887123536438386009406733953603895427104, 5986310706529156424445550203935671055135705478463552] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), B1544, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1543 : B1543.tree = HexagonCover.NBand.M7500_7700.SplitData.node1543 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1544
  · rfl
  · rfl

def B1542 : Block := .branch 170 ![5193564509135055857931993032425857, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 5986310706529156424445550513420680876480774203244608] ![(.leaf 0 (Common.fact 536).pointIds 536), (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), B1543, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1542 : B1542.tree = HexagonCover.NBand.M7500_7700.SplitData.node1542 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1543
  · rfl

def B1541 : Block := .branch 100 ![5192296858534827628530496329220481, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 5986310706529156424445550513420680876480774203244608] ![B1542, (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq1541 : B1541.tree = HexagonCover.NBand.M7500_7700.SplitData.node1541 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1542
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1540 : Block := .branch 107 ![5192296858534827628530496329220481, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 5986310706529156424445550513420680876480774203244608] ![(.leaf 0 (Common.fact 303).pointIds 303), (.leaf 1 (Common.fact 304).pointIds 304), (.leaf 2 (Common.fact 305).pointIds 305), B1541, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 307).pointIds 307), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq1540 : B1540.tree = HexagonCover.NBand.M7500_7700.SplitData.node1540 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1541
  · rfl
  · rfl
  · rfl

def B1539 : Block := .branch 112 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 5986310706529156424445550513420680876480774203244608] ![B1540, (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq1539 : B1539.tree = HexagonCover.NBand.M7500_7700.SplitData.node1539 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1540
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1538 : Block := .branch 118 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 5986310706529156424445550513420680876480774203244608] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), B1539, (.leaf 4 (Common.fact 763).pointIds 763), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq1538 : B1538.tree = HexagonCover.NBand.M7500_7700.SplitData.node1538 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1539
  · rfl
  · rfl
  · rfl

def B1537 : Block := .branch 128 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 5986310706529156424445550513420680876480774203244608] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B1538, (.leaf 4 (Common.fact 765).pointIds 765), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq1537 : B1537.tree = HexagonCover.NBand.M7500_7700.SplitData.node1537 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1538
  · rfl
  · rfl
  · rfl

def B1536 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 879).pointIds 879), B1537]
theorem treeEq1536 : B1536.tree = HexagonCover.NBand.M7500_7700.SplitData.node1536 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1537

def B1535 : Block := .branch 151 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B1536, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq1535 : B1535.tree = HexagonCover.NBand.M7500_7700.SplitData.node1535 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1536
  · rfl
  · rfl

def B1534 : Block := .branch 132 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B1535]
theorem treeEq1534 : B1534.tree = HexagonCover.NBand.M7500_7700.SplitData.node1534 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1535

def B1533 : Block := .branch 101 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 32667107224727469445613615407891089981504] ![B1534, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq1533 : B1533.tree = HexagonCover.NBand.M7500_7700.SplitData.node1533 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1534
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1532 : Block := .branch 133 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B1533]
theorem treeEq1532 : B1532.tree = HexagonCover.NBand.M7500_7700.SplitData.node1532 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1533

def B1531 : Block := .branch 157 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1532, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq1531 : B1531.tree = HexagonCover.NBand.M7500_7700.SplitData.node1531 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1532
  · rfl
  · rfl

def B1530 : Block := .branch 125 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 964).pointIds 964), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B1531, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq1530 : B1530.tree = HexagonCover.NBand.M7500_7700.SplitData.node1530 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1531
  · rfl

theorem accepted1530 : B1530.accepted = true := by decide +kernel
theorem checked1530 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1530 (maskNeeds ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1530]
  exact B1530.sound accepted1530
#print axioms checked1530

def Tip1527_1530 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1530 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1530
def B1554 : Block := .branch 138 ![385, 1538, 6148, 79228162514264337593543974920, 5986310712082564652594948860189824816672790072623120, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 981).pointIds 981), (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 982).pointIds 982)]
theorem treeEq1554 : B1554.tree = HexagonCover.NBand.M7500_7700.SplitData.node1554 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1553 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 5575186299632655785383929568162090376593424, 393248, 1461501659108974402728309820215408373624055791680] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1554, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 980).pointIds 980)]
theorem treeEq1553 : B1553.tree = HexagonCover.NBand.M7500_7700.SplitData.node1553 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1554
  · rfl
  · rfl

def B1552 : Block := .branch 100 ![1496577676626844598625169461651207639949217380696449, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 5575186299632655785383929568162090376593424, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1553]
theorem treeEq1552 : B1552.tree = HexagonCover.NBand.M7500_7700.SplitData.node1552 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1553

def B1551 : Block := .branch 159 ![1496577676626844598625169461651207639949217380696449, 302821894829204075185666, 18446884811197913092, 79266848140492005727134572552, 5575186299632655785383929568162090376593424, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 977).pointIds 977), (.leaf 1 (Common.fact 978).pointIds 978), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 500).pointIds 500), (.leaf 4 (Common.fact 501).pointIds 501), (.leaf 5 (Common.fact 502).pointIds 502), B1552]
theorem treeEq1551 : B1551.tree = HexagonCover.NBand.M7500_7700.SplitData.node1551 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1552

def B1550 : Block := .branch 170 ![10384596192949733827821542456689025, 302821894829204075185666, 18446884811197913092, 79266848140492005727134572552, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 1461501659108974401461123447501910989730439757888] ![B1551, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1550 : B1550.tree = HexagonCover.NBand.M7500_7700.SplitData.node1550 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1551
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1549 : Block := .branch 171 ![10384596192949733827821542456689025, 302821894829204075185666, 18446884811197913092, 79266848140492005727134572552, 5575186299632655785383929568162090376593424, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1550, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1549 : B1549.tree = HexagonCover.NBand.M7500_7700.SplitData.node1549 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1550
  · rfl

def B1548 : Block := .branch 142 ![10384596192949733827821542456689025, 302821894829204075185666, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1549, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq1548 : B1548.tree = HexagonCover.NBand.M7500_7700.SplitData.node1548 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1549
  · rfl
  · rfl

def B1547 : Block := .branch 144 ![10384596192949733827821542456689025, 302821894829204075185666, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1548, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq1547 : B1547.tree = HexagonCover.NBand.M7500_7700.SplitData.node1547 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1548
  · rfl

def B1546 : Block := .branch 160 ![10384596192949733827821542456689025, 302821894829204075185666, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 958).pointIds 958), (.leaf 2 (Common.fact 883).pointIds 883), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), B1547]
theorem treeEq1546 : B1546.tree = HexagonCover.NBand.M7500_7700.SplitData.node1546 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1547

def B1529 : Block := .branch 69 ![10384596192949733827821542456689025, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip1527_1530, B1546, (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq1529 : B1529.tree = HexagonCover.NBand.M7500_7700.SplitData.node1529 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1546
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1528 : Block := .branch 91 ![10384593717069655257060992658440577, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1529, (.leaf 1 (Common.fact 338).pointIds 338), (.leaf 2 (Common.fact 339).pointIds 339), (.leaf 3 (Common.fact 340).pointIds 340), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq1528 : B1528.tree = HexagonCover.NBand.M7500_7700.SplitData.node1528 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1529
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1527 : Block := .branch 113 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1528, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq1527 : B1527.tree = HexagonCover.NBand.M7500_7700.SplitData.node1527 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1528
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1527 : B1527.accepted = true := by decide +kernel
theorem checked1527 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1527 (maskNeeds ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1527]
  exact B1527.sound accepted1527
#print axioms checked1527

def Tip1464_1468 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1468 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1468
def Tip1464_1527 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1527 ![385, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1527
def B1526 : Block := .branch 108 ![385, 1538, 6148, 79247505327378171660339273736, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 910).pointIds 910), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq1526 : B1526.tree = HexagonCover.NBand.M7500_7700.SplitData.node1526 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1525 : Block := .branch 109 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 1461501659108974401460815095860045533376566263872] ![(.leaf 0 (Common.fact 904).pointIds 904), (.leaf 1 (Common.fact 905).pointIds 905), (.leaf 2 (Common.fact 906).pointIds 906), (.leaf 3 (Common.fact 907).pointIds 907), B1526, (.leaf 5 (Common.fact 908).pointIds 908), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq1525 : B1525.tree = HexagonCover.NBand.M7500_7700.SplitData.node1525 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1526
  · rfl
  · rfl

def B1524 : Block := .branch 160 ![385, 302821750714015999329794, 18446884811197913092, 79247505327378171660339273736, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 958).pointIds 958), (.leaf 2 (Common.fact 883).pointIds 883), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), B1525]
theorem treeEq1524 : B1524.tree = HexagonCover.NBand.M7500_7700.SplitData.node1524 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1525

def B1523 : Block := .branch 69 ![1496577676626887123536438386009406733953603895034241, 302231454903657293678082, 18446884811197913092, 79247505327378171660339273736, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 956).pointIds 956), B1524, (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq1523 : B1523.tree = HexagonCover.NBand.M7500_7700.SplitData.node1523 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1524
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1522 : Block := .branch 125 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 79247505327378171660339273736, 98320, 2854495385411919762116571938898990272765886496, 21778071483257439748153583858789358501952] ![B1523, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq1522 : B1522.tree = HexagonCover.NBand.M7500_7700.SplitData.node1522 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1523
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1521 : Block := .branch 151 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 18446884811197913092, 79247505327378171660339273736, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1522, (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq1521 : B1521.tree = HexagonCover.NBand.M7500_7700.SplitData.node1521 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1522
  · rfl

def B1520 : Block := .branch 170 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 21778071483257439748153583858789358501952] ![B1521, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1520 : B1520.tree = HexagonCover.NBand.M7500_7700.SplitData.node1520 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1521
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1519 : Block := .branch 171 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1520, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1519 : B1519.tree = HexagonCover.NBand.M7500_7700.SplitData.node1519 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1520
  · rfl

def B1518 : Block := .branch 172 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1519, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq1518 : B1518.tree = HexagonCover.NBand.M7500_7700.SplitData.node1518 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1519
  · rfl
  · rfl

def B1467 : Block := .branch 80 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1464_1468, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 934).pointIds 934), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 936).pointIds 936), B1518]
theorem treeEq1467 : B1467.tree = HexagonCover.NBand.M7500_7700.SplitData.node1467 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1518

def B1466 : Block := .branch 76 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 931).pointIds 931), B1467, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), Tip1464_1527]
theorem treeEq1466 : B1466.tree = HexagonCover.NBand.M7500_7700.SplitData.node1466 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1467
  · rfl
  · rfl
  · rfl
  · rfl

def B1465 : Block := .branch 149 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1466, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq1465 : B1465.tree = HexagonCover.NBand.M7500_7700.SplitData.node1465 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1466
  · rfl
  · rfl

def B1464 : Block := .branch 88 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1465]
theorem treeEq1464 : B1464.tree = HexagonCover.NBand.M7500_7700.SplitData.node1464 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1465

theorem accepted1464 : B1464.accepted = true := by decide +kernel
theorem checked1464 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1464 (maskNeeds ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1464]
  exact B1464.sound accepted1464
#print axioms checked1464

end HexagonCover.NBand.M7500_7700.SplitTree.Run0019
