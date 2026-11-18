# Why a seventh triangle cannot cover a larger hexagon

[English overview](../README.en.md) · [한국어](proof-guide.md)

Six unit equilateral triangles tile a regular hexagon of side 1. Add a seventh and allow every triangle to move and rotate freely, overlap the others, or extend beyond the hexagon. How much larger a regular hexagon can they cover? **No side length greater than 1 is possible.** Jineon Baek and Jeewon Kim gave an earlier proof. This guide follows the proof by contradiction developed in this project. [Comparison of the two proofs](proof-comparison.en.md) · [Formal statement and the side-1 example](../lean/HexagonCover/FinalTheorem.lean)

## 1. Each triangle has to cover a particular point

Suppose seven closed unit equilateral triangles cover a regular hexagon $H_s$ of side $s>1$. Take its center and its six vertices. Every pair of these seven points is at least $s$ apart, and the diameter of each triangle is 1. Each triangle must therefore cover exactly one of the seven points. Write $C$ for the triangle covering the center and $T_0,\ldots,T_5$ for those covering the vertices in cyclic order.

Place a concentric regular hexagon $H_1$ of side 1 inside $H_s$, with corresponding sides parallel, and let $u_i$ denote its vertices. Set $\delta=s-1$. The same triangle $C$ contains the closed disk of radius $\delta$ about the origin, and each $T_i$ contains the closed disk of radius $\delta/2$ about $u_i$. For example, a point less than $\delta$ from the origin is more than 1 from every vertex of $H_s$. Only $C$ can cover it. Closedness extends the conclusion to the boundary of the disk. We can now study $H_1$ while keeping all seven triangles in their original positions. The positive disk radii are what distinguish this situation from the familiar tiling at $s=1$. [Assigned vertices and forced disks](../lean/HexagonCover/Anchors.lean)

## 2. Covering the boundary costs area outside the hexagon

Starting at $u_i$, let $a_i$ be the length that $T_i$ covers along the side toward $u_{i-1}$, and $b_i$ the length it covers toward $u_{i+1}$. Call $T_i$ *heavy* if $a_i+b_i\geq1$. A unit equilateral triangle has area $\Delta=\sqrt{3}/4$. The seven triangles together have area $7\Delta$, and $H_1$ needs $6\Delta$. Even counting overlapping portions with multiplicity, the sum of their areas outside $H_1$ is at most $\Delta$. A single heavy outer triangle spends at least $\Delta\max(a_i,b_i)^2$ of that allowance. [Area bound](../lean/HexagonCover/AreaBudget.lean) · [Exterior area of one triangle](../lean/HexagonCover/ExteriorLoss.lean)

Call an outer triangle *nonpenetrating* if it avoids the **open** disk of radius $1/2$ about the origin. Tangency is allowed. The written proof rules out two such triangles by considering the three possible cyclic distances between their vertices. Its three certificates use 139,690 geometric contradictions in total. The order of the boundary reaches and the area bound then force a unique heavy outer triangle, which is nonpenetrating. The main Lean theorem derives the properties it needs by a separate argument, so the three certificates form an appendix to the written proof. [Uniqueness in an actual covering](../lean/HexagonCover/GlobalMinimum.lean) · [Normalization and reach inequalities](../lean/HexagonCover/NormalizedHeavy.lean)

By rotating or reflecting the entire configuration, label the heavy triangle $T_5$ and its longer reach $M=b_5$. Each of the twelve reaches is at least $1-M$. The sum $a_5+b_5$ is strictly greater than 1, while each of the other five sums is strictly less than 1. These reaches also force $C$ to contain a disk about the origin of radius $\rho(1-M)$, where $\rho(t)=1-\sqrt{1-t+t^2}$. The remaining steps ask what **this same triangle** must cover in addition to that disk. [Disk forced into the central triangle](../lean/HexagonCover/CentralDisk.lean)

## 3. A gap left by the outer triangles forces the center to the boundary

Write $E_i=[u_i,u_{i+1}]$ with indices taken modulo six. The two outer triangles at its ends cover lengths $b_i$ and $a_{i+1}$. If their sum is less than 1, they leave a gap of positive length that $C$ must cover. The boundary sides touched by $C$ are contained in a pair of adjacent sides, and the outer triangles already cover all of $E_5$ on the long-reach side. This leaves nine possible nonempty sets of gapped sides.

$$
\{0\},\ \{1\},\ \{2\},\ \{3\},\ \{4\},\quad
\{0,1\},\ \{1,2\},\ \{2,3\},\ \{3,4\}.
$$

Use coordinates in which $u_5=(1,0)$ and $u_0$ is its upper neighbor. Write $h=\sqrt{3}/2$. In eight cases both $R=(7/10,h/7)$ and an endpoint of an actual gap must lie in $C$. They are more than 1 apart, contradicting the diameter of $C$. [The eight gap cases](../lean/HexagonCover/GapExclusions.lean)

When $E_4$ contains the only gap, the proof asks whether $A=(-19/100,0)$ belongs to the closed triangle $T_2$. If $A$ lies outside $T_2$, four points are forced into $T_1$ and every equilateral triangle enclosing them has side length greater than 1. If $A$ belongs to $T_2$ (including on its boundary), the proof forces $P=(0,-ha_5)$ into the interior of $T_4$. In every possible orientation of $T_4$, the required contacts conflict with the disk already forced into $C$. [The two cases for the single gap on $E_4$](../lean/HexagonCover/E4Complete.lean)

## 4. With no gaps, the longer reach determines the last two cases

Suppose the outer triangles cover all six sides. The area bound and the successive boundary reaches of the five light triangles give $M^2+5(1-M)^2<1$, hence $M>2/3$. Each assigned vertex lies in the interior of its triangle, giving $M<1$.

- **Longer reach, $\sqrt{3}/2\leq M<1$.** Choose two points on the inward-facing supporting line of $T_5$. Distances to the boundary endpoints of other outer triangles show that points missed by all six outer triangles occur arbitrarily close to each of the two chosen points. The missed points must belong to $C$, so closedness puts both limit points in $C$ as well. But their positions and the disk of radius $\rho(1-M)$ require more room than a unit equilateral triangle can provide in any orientation. The written proof establishes this in three intervals. Lean combines the inequalities for the two points and the disk across the entire high range. [Why both points belong to $C$](../lean/HexagonCover/HighMActual.lean) · [High-reach theorem](../lean/HexagonCover/HighMUpper.lean)
- **Shorter reach, $2/3<M<\sqrt{3}/2$.** Cover this range with eleven closed intervals. Within each interval the area and boundary inequalities give points that specific triangles must contain. If $L$ is the left endpoint, the distance from the origin to **the whole triangle** $T_5$ must be at least $\sqrt{3}L/2$. A tree then asks which triangle covers each additional test point, branching over the possible answers. An actual covering would supply an answer at every step along some path. Every path ends in an exact contradiction for the points accumulated by one triangle. A pair may be more than 1 apart, the smallest enclosing equilateral triangle may be too large over all orientations, or a triangle containing the assigned points may be unable to avoid the required open disk. [Why the branching argument is sound](../lean/HexagonCover/OwnerTree.lean) · [The eleven intervals](../lean/HexagonCover/NVerifiedBands.lean)

The eleven certified intervals together cover $[2/3,87/100]$. Their upper endpoint satisfies $(87/100)^2>3/4$, so the two arguments overlap. The final Lean proof applies the tree when $M\leq87/100$ and the high-reach theorem otherwise. This exhausts both the possible boundary gaps and every reach compatible with having no gaps. The assumed covering of $H_s$ for $s>1$ therefore cannot exist. [Final assembly](../lean/HexagonCover/FinalTheorem.lean) · [Theorem for arbitrary rigid placements](../lean/HexagonCover/SemanticFinal.lean)

## Checking the theorem and the 105-point example

The Lean project gives the definitions and formal proof for the **whole hexagon**. One low-reach interval also yields a separate question about **105 fixed points**. With the stated distance bound on $T_5$ every assignment fails. Removing that bound allows an explicit placement of seven triangles satisfying all the point and role requirements. The finite checker verifies the placement and the exclusion from exact data. [Build the Lean theorem](../lean/README.md) · [Reproduce both 105-point results](../finite/README.md)
