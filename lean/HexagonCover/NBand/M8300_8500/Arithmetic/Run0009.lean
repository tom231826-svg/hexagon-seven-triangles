import HexagonCover.NBand.M8300_8500.Semantics
import HexagonCover.NISubsetData.Batch0007
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.Arithmetic.Run0009
open Common Semantics DistanceLeaf

theorem checked_1588 : CheckedFact 1588 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1588) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1597 : CheckedFact 1597 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1597) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_1605 : CheckedFact 1605 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1605) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1610 : CheckedFact 1610 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1610) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1613 : CheckedFact 1613 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1613) (positions := (3,6))
      (by decide +kernel) T contained

theorem checked_1614 : CheckedFact 1614 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1614) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1615 : CheckedFact 1615 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1615) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1617 : CheckedFact 1617 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1617) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1618 : CheckedFact 1618 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1618) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1619 : CheckedFact 1619 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1619) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_1620 : CheckedFact 1620 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1620) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1621 : CheckedFact 1621 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1621) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1622 : CheckedFact 1622 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1622) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1623 : CheckedFact 1623 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1623) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1626 : CheckedFact 1626 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1626) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1637 : CheckedFact 1637 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1637) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1641 : CheckedFact 1641 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1641) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1642 : CheckedFact 1642 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1642) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1645 : CheckedFact 1645 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1645) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1646 : CheckedFact 1646 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1646) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1654 : CheckedFact 1654 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1654) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1656 : CheckedFact 1656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1656) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1657 : CheckedFact 1657 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1657) (positions := (3,4))
      (by decide +kernel) T contained

theorem checked_1658 : CheckedFact 1658 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1658) (positions := (3,4))
      (by decide +kernel) T contained

theorem checked_1681 : CheckedFact 1681 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0007.c0004_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_1684 : CheckedFact 1684 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1684) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1685 : CheckedFact 1685 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1685) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1686 : CheckedFact 1686 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1686) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1687 : CheckedFact 1687 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1687) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1689 : CheckedFact 1689 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1689) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1690 : CheckedFact 1690 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1690) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1693 : CheckedFact 1693 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1693) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1694 : CheckedFact 1694 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1694) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1695 : CheckedFact 1695 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1695) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1696 : CheckedFact 1696 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1696) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1697 : CheckedFact 1697 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1697) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1698 : CheckedFact 1698 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1698) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1699 : CheckedFact 1699 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1699) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1700 : CheckedFact 1700 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1700) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1701 : CheckedFact 1701 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1701) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1702 : CheckedFact 1702 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1702) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1703 : CheckedFact 1703 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1703) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1704 : CheckedFact 1704 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1704) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1705 : CheckedFact 1705 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1705) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1706 : CheckedFact 1706 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1706) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1707 : CheckedFact 1707 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1707) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1708 : CheckedFact 1708 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1708) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1709 : CheckedFact 1709 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1709) (positions := (21,27))
      (by decide +kernel) T contained

theorem checked_1710 : CheckedFact 1710 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1710) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1711 : CheckedFact 1711 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1711) (positions := (21,27))
      (by decide +kernel) T contained

theorem checked_1717 : CheckedFact 1717 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1717) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1719 : CheckedFact 1719 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1719) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1720 : CheckedFact 1720 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1720) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1721 : CheckedFact 1721 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1721) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1732 : CheckedFact 1732 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1732) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1736 : CheckedFact 1736 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1736) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1738 : CheckedFact 1738 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1738) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1739 : CheckedFact 1739 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1739) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1740 : CheckedFact 1740 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1740) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1741 : CheckedFact 1741 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1741) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1747 : CheckedFact 1747 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1747) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1748 : CheckedFact 1748 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1748) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1749 : CheckedFact 1749 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1749) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1755 : CheckedFact 1755 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1755) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1762 : CheckedFact 1762 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1762) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1763 : CheckedFact 1763 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1763) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1764 : CheckedFact 1764 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1764) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1775 : CheckedFact 1775 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1775) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1782 : CheckedFact 1782 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1782) (positions := (4,7))
      (by decide +kernel) T contained

theorem checked_1784 : CheckedFact 1784 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1784) (positions := (21,25))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8300_8500.Arithmetic.Run0009
