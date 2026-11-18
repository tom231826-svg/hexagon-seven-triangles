# How the proof differs from Baek and Kim’s

[English overview](../README.en.md) · [한국어](proof-comparison.md) · [English proof guide](proof-guide.en.md)

Jineon Baek and Jeewon Kim proved that seven closed unit equilateral triangles, each free to rotate and translate, cannot cover a regular hexagon of side $s>1$. Their manuscript dated September 24, 2026, and Baek’s Lean formalization dated September 27 both precede this project’s November 11 proof record. The comparison below follows their 69-page manuscript and our written geometric and computational proof. [Baek and Kim’s manuscript](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/arrange/paper_draft/main.pdf) · [Baek’s Lean theorem](https://github.com/jcpaik/hexagon-cover-formalization/blob/545a609e0225e664dc830310641f2ec0170ee181/HexagonCover/ClosedScaling.lean#L29-L51)

In our proof, $C$ denotes the triangle covering the center. The outer triangles $T_0,\ldots,T_5$ are labeled by the hexagon vertices they cover. Write $E_i=[u_i,u_{i+1}]$ for a side of the concentric unit hexagon, with indices taken modulo six. A *gap* is a part of that side missed by the outer triangles at its two ends. The *reach* of an outer triangle along a side is the length it covers starting at its assigned vertex. We label the unique outer triangle whose two reaches sum to more than one as $T_5$. Its longer reach is $M$.

## 1. A side has a gap

Both proofs use the same obligation. The central triangle must cover the boundary left by the outer triangles, while still containing the points already forced into it.

Baek and Kim split cases according to which triangles cover the midpoints of the six segments from the center to the vertices. We divide the proof into nine patterns according to which sides have a positive-length gap. Eight patterns force two points more than one unit apart into $C$. When $E_4$ alone has a gap, we ask whether the closed triangle $T_2$ contains $A=(-19/100,0)$. If it does, contact among the covering triangles forces a condition on $C$ incompatible with the disk it must contain. If $A$ lies outside $T_2$, four points are forced into the same outer triangle $T_1$.

This identifies which triangle fails in each gap pattern. Baek and Kim’s gap argument uses only the hexagon boundary and the six segments from its center to its vertices. It also treats a single boundary point missed by the two open outer triangles. Our argument uses coverage of the hexagon interior as well. In the sole-$E_4$ case, our proof explains why the four points must all belong to $T_1$. Once that assignment is known, the formulas in Baek and Kim’s appendix can also show that one unit triangle cannot contain those four points. [Their gap classification](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/arrange/paper_draft/07_exhaustive_assembly.tex#L10-L24) · [Their boundary and radial formulas](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/arrange/paper_draft/A_structural_shared_local_signed_center_optimization.tex#L610-L729) · [Our gap exclusion in Lean](../lean/HexagonCover/E4Complete.lean)

## 2. All sides are covered by the outer triangles and $M$ is large

Both proofs identify interior points that the outer triangles must leave to $C$ when they cover the boundary. They then ask whether a single unit equilateral triangle can contain those points together with a disk.

Baek and Kim choose nine points whose positions depend on where adjacent triangles pass coverage of a side from one triangle to the other. All nine must lie in $C$. Six give a disk inside their convex hull, and the remaining three complete the contradiction. Our written proof takes two points on the inward-facing support line of $T_5$. The exclusions use different geometric data in three ranges.

| Range of $M$ | Data used to exclude other triangles from covering the two points |
|---|---|
| $[\sqrt{3}/2,0.90)$ | The endpoints of the boundary intervals actually covered by $T_0$ and $T_4$. |
| $[0.90,0.95)$ | The shorter reach of $T_5$ and the boundary endpoint of $T_0$. |
| $[0.95,1)$ | Distances to $u_4$, **the hexagon vertex assigned to $T_4$**, and to the boundary endpoint of $T_0$. |

Baek and Kim’s nine-point argument handles the full no-gap range in one step. Our written proof needs three ranges for large $M$ alone. The threshold inequality also looks different. A minimum enclosing side length of at least one suffices to exclude an *open* unit triangle. To exclude a *closed* unit triangle, our proof needs a minimum strictly greater than one. Scaling gives equivalent versions of the original theorem. [Their nine-point argument](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/arrange/paper_draft/06_finite_enclosure_full.tex#L405-L559) · [Our Lean treatment combining the high-$M$ cases](../lean/HexagonCover/HighMUpper.lean)

## 3. All sides are covered by the outer triangles and $M$ is small

Both proofs select finitely many points that any cover must include. Baek and Kim force all nine into $C$. We fix point coordinates separately on eleven intervals whose union contains $2/3<M<\sqrt{3}/2$. Whenever several triangles might cover a point, the certificate branches on the choice. Each branch keeps all points assigned to a given triangle together. Exact arithmetic eventually shows that at least one triangle cannot meet its obligations.

This yields a finite statement that can be tested without assuming coverage of the whole hexagon. It requires a separate point list and a branching certificate for each interval. Baek and Kim’s earlier research records already discuss finite sets, assignments of points to triangles, and fixed rational witnesses on parameter intervals. [Their finite-point proposal](https://github.com/dylan0301/hexagon-cover-database/blob/26c0abe355394047b2da90be80d96ee3830e55fd/prompts/20260603prooftreeExample.txt#L54-L60) · [Their interval witnesses](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/proof/3XXX_CE0/31XX_Nplus1/310X_all_Vd0/3102X_fable5proof/ab-set/hole_set_noncover.md#L267-L288) · [Our eleven-interval theorem](../lean/HexagonCover/NVerifiedBands.lean)

The example drawn from $[0.81,0.83]$ has 105 fixed points. A triangle is prescribed for each of 39 points, and any of the seven may cover each of the remaining 66. If the distance from the origin to **the whole closed triangle $T_5$** is at least $81\sqrt{3}/200$, covering all 105 is impossible. Removing that single condition gives an explicit covering of exactly the same input, with every prescribed role still respected. The interval identifies where we obtained the point list. The finite problem imposes no bound on the actual reaches of the seven triangles. [Coordinates, placement and both exact checks](../finite/README.md)

In the public sources we reviewed through November 18, 2026, we found no argument giving this specific finite-point exclusion under the clearance condition. We could inspect only parts of the argument attributed to the 105-page manuscript P2 in the September 26 hybrid proof, and later accounts of the 2005 Karabash–Soifer paper. Priority for the finite result remains open. [P2 bibliographic entry, page 16](https://raw.githubusercontent.com/jcpaik/hexagon-cover-formalization/545a609e0225e664dc830310641f2ec0170ee181/hexagon_hybrid_proof.pdf#page=16) · [2005 journal contents](https://geombina.uccs.edu/past-issues/volume-xv)
