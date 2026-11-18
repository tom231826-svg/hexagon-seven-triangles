import HexagonCover.NBand.M8300_8500.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.Arithmetic.Run0008
open Common Semantics DistanceLeaf

theorem checked_1371 : CheckedFact 1371 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1371) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1372 : CheckedFact 1372 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1372) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1375 : CheckedFact 1375 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1375) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1379 : CheckedFact 1379 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1379) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1380 : CheckedFact 1380 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1380) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1381 : CheckedFact 1381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1381) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1382 : CheckedFact 1382 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1382) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1383 : CheckedFact 1383 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1383) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1384 : CheckedFact 1384 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1384) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1387 : CheckedFact 1387 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1387) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1397 : CheckedFact 1397 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1397) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1398 : CheckedFact 1398 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1398) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1399 : CheckedFact 1399 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1399) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1400 : CheckedFact 1400 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1400) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1401 : CheckedFact 1401 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1401) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1402 : CheckedFact 1402 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1402) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1403 : CheckedFact 1403 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1403) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1404 : CheckedFact 1404 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1404) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1405 : CheckedFact 1405 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1405) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1408 : CheckedFact 1408 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1408) (positions := (3,4))
      (by decide +kernel) T contained

theorem checked_1412 : CheckedFact 1412 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1412) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_1413 : CheckedFact 1413 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1413) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1414 : CheckedFact 1414 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1414) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1415 : CheckedFact 1415 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1415) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1417 : CheckedFact 1417 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1417)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1429 : CheckedFact 1429 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1429) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_1438 : CheckedFact 1438 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1438) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1439 : CheckedFact 1439 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1439) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1440 : CheckedFact 1440 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1440) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1441 : CheckedFact 1441 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1441) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1443 : CheckedFact 1443 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1443) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1444 : CheckedFact 1444 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1444) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1445 : CheckedFact 1445 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1445) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1446 : CheckedFact 1446 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1446) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1447 : CheckedFact 1447 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1447) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1448 : CheckedFact 1448 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1448) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1449 : CheckedFact 1449 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1449) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1451 : CheckedFact 1451 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1451) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1452 : CheckedFact 1452 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1452) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1453 : CheckedFact 1453 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1453) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1454 : CheckedFact 1454 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1454) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1455 : CheckedFact 1455 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1455) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1456 : CheckedFact 1456 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1456) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1457 : CheckedFact 1457 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1457) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1458 : CheckedFact 1458 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1458) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1459 : CheckedFact 1459 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1459) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1464 : CheckedFact 1464 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1464) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1465 : CheckedFact 1465 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1465) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1468 : CheckedFact 1468 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1468) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_1469 : CheckedFact 1469 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1469) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1470 : CheckedFact 1470 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1470) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1477 : CheckedFact 1477 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1477) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1479 : CheckedFact 1479 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1479) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1488 : CheckedFact 1488 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1488) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1489 : CheckedFact 1489 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1489) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1496 : CheckedFact 1496 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1496) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1497 : CheckedFact 1497 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1497) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1498 : CheckedFact 1498 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1498) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1503 : CheckedFact 1503 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1503) (positions := (3,6))
      (by decide +kernel) T contained

theorem checked_1505 : CheckedFact 1505 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1505) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1510 : CheckedFact 1510 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1510) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1511 : CheckedFact 1511 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1511) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1512 : CheckedFact 1512 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1512) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1513 : CheckedFact 1513 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1513) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_1514 : CheckedFact 1514 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1514) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1515 : CheckedFact 1515 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1515) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1517 : CheckedFact 1517 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1517) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1518 : CheckedFact 1518 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1518) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1519 : CheckedFact 1519 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1519) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1521 : CheckedFact 1521 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1521) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_1525 : CheckedFact 1525 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1525) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1526 : CheckedFact 1526 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1526) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1531 : CheckedFact 1531 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1531) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1532 : CheckedFact 1532 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1532) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1537 : CheckedFact 1537 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1537) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1538 : CheckedFact 1538 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1538) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1539 : CheckedFact 1539 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1539) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1540 : CheckedFact 1540 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1540) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1542 : CheckedFact 1542 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1542) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1543 : CheckedFact 1543 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1543) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1547 : CheckedFact 1547 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1547) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1548 : CheckedFact 1548 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1548) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1554 : CheckedFact 1554 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1554) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1555 : CheckedFact 1555 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1555) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1561 : CheckedFact 1561 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1561) (positions := (4,7))
      (by decide +kernel) T contained

theorem checked_1563 : CheckedFact 1563 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1563) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1564 : CheckedFact 1564 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1564) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1565 : CheckedFact 1565 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1565) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1566 : CheckedFact 1566 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1566) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1567 : CheckedFact 1567 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1567) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1568 : CheckedFact 1568 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1568) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1569 : CheckedFact 1569 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1569) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1570 : CheckedFact 1570 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1570) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_1582 : CheckedFact 1582 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1582) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_1584 : CheckedFact 1584 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1584) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1586 : CheckedFact 1586 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1586) (positions := (21,24))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8300_8500.Arithmetic.Run0008
