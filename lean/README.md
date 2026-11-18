# Lean proof of the hexagon theorem

The source proves that for every real side length $s>1$, seven independently placed closed unit equilateral triangles fail to cover the closed regular hexagon. The formal statement allows overlapping triangles, repeated placements, and triangles extending beyond the hexagon. At $s=1$, six radial triangles give a cover and a seventh triangle may duplicate one of them.

| What to inspect | Source |
|---|---|
| Vertices, Euclidean plane, convex hulls and covering predicate | [Geometry.lean](HexagonCover/Geometry.lean) |
| Final contradiction, strict inequality $s>1$, and the $s=1$ cover | [FinalTheorem.lean](HexagonCover/FinalTheorem.lean) |
| Equivalence with arbitrary rigid placements and arbitrary pose of the hexagon | [SemanticFinal.lean](HexagonCover/SemanticFinal.lean) |
| Assembly of the eleven low-reach cases | [NVerifiedBands.lean](HexagonCover/NVerifiedBands.lean) |
| Axiom check and validation targets | [FinalValidation.lean](HexagonCover/FinalValidation.lean) |

## Check the source

Use Git and [Elan](https://github.com/leanprover/elan) to run the pinned Lean 4.35.0 toolchain. From the repository root, run these commands on a machine with enough storage for mathlib and compiled proofs.

```sh
cd lean
lake exe cache get
python3 build.py
```

The Python 3 script verifies the source checksums, orders all 1,017 modules needed by the explicit rigid-placement theorem, and compiles each of them, one at a time, using a single Lean thread. Its final module prints the axioms of the theorem and its equivalence with the canonical statement. To check the setup quickly, use `python3 build.py --target geometry`. To include all 1,041 modules and the certificate rejection tests, use `python3 build.py --target all`. Each run recompiles its full selected local dependency chain.

The dependency versions are recorded in [lake-manifest.json](lake-manifest.json). The mathlib cache supplies precompiled external dependencies. Readers who prefer Lake’s own scheduling and incremental builds can run `lake build +HexagonCover.SemanticFinal:olean`. For a 16 GB machine the sequential script gives more predictable memory use.

## Verification history and scope

The project's November 17, 2026 clean build started with an empty local object directory. It compiled 1,041 local modules comprising 134,860,827 bytes of Lean source and reused the pinned external package cache. The recorded compiler CPU time was about 3 hours 39 minutes. The final checks found only the standard Lean axioms `propext`, `Quot.sound`, and `Classical.choice`. The clean proof export was also checked in a fresh environment with the official Lean C++ kernel. The export had SHA-256 `c5ee94f68864a56983f628cf67d46d4a514386b3d4e54e35712233546127252b`.

All 1,041 project modules and all three Lake/toolchain files in this directory were compared byte for byte by SHA-256 to the frozen source inventory for that build. To check the release files on macOS use `shasum -a 256 -c SHA256SUMS`; on Linux use `sha256sum -c SHA256SUMS`.

For this release, a fresh Git clone was used to recompile `FinalTheorem` and `SemanticFinal`. Each of their 1,015 prerequisite modules was matched by source and compiled-object hash against the earlier clean build. Both newly compiled objects matched the earlier hashes, and Lean printed the same three axioms for all nine inspected declarations. In a second fresh clone, `python3 build.py --target geometry` compiled the first geometric module from zero local project objects. These release checks reused the pinned external dependencies already on the machine. The complete clean local build and fresh-kernel replay above were performed on November 17. [Recorded versions, hashes, targets, and verification scope](verification.json)

The formalization follows the written proof of this project and gives alternative arguments at several steps, including the heavy outer triangle, high-reach residual points, and contacts at edge E4. Its final theorem uses the eleven low-reach cases. The original written proof also has a separate three-case appendix with 139,690 contradictions. That appendix is outside the final Lean theorem's dependency chain. The fixed 105-point clearance comparison has separate evidence in the repository.
