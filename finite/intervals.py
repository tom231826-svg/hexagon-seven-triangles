"""Consumer of full-angle interval witnesses in rational arithmetic.

Extracted from the project’s independent nonpenetration checker.
Input coordinates are (x, y + z*sqrt(3)). Radius arguments are squared.
"""
from __future__ import annotations

from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path


SCHEMA = "separate-rational-interval-ni-v1"
SQRT_BITS = 100
VERTEX_PAIRS = ((0, 1), (1, 2), (2, 0))
EDGES = ((0, 1), (1, 2), (2, 0))


class Rejected(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


def fraction(value):
    if type(value) is Q:
        return value
    require(type(value) is str and len(value) < 10000, "rational string required")
    answer = Q(value)
    require(str(answer) == value, "noncanonical rational string")
    return answer


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unique_object(pairs):
    result = dict(pairs)
    require(len(result) == len(pairs), "duplicate JSON key")
    return result


def load(path):
    def no_constant(value):
        raise Rejected("nonfinite JSON constant " + value)
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object,
                      parse_constant=no_constant)


def normalized_input(values, radius_squared):
    require(type(values) in (list, tuple) and bool(values), "nonempty point list required")
    points = []
    for value in values:
        require(type(value) in (list, tuple) and len(value) == 3, "point must be a triple")
        points.append(tuple(fraction(c) for c in value))
    radius = fraction(radius_squared)
    require(radius > 0, "positive exact squared radius required")
    record = {"points": [[str(c) for c in p] for p in points],
              "radius_squared": str(radius)}
    return points, radius, hashlib.sha256(canonical(record)).hexdigest()


# Closed rational intervals. No floating operation occurs in a proof bound.
def point_interval(x):
    return x, x


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]


def minus(a, b):
    return a[0] - b[1], a[1] - b[0]


def times(a, b):
    candidates = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
    return min(candidates), max(candidates)


def scale(a, factor):
    return (a[0]*factor, a[1]*factor) if factor >= 0 else (a[1]*factor, a[0]*factor)


def square(a):
    maximum = max(a[0]*a[0], a[1]*a[1])
    minimum = Q(0) if a[0] <= 0 <= a[1] else min(a[0]*a[0], a[1]*a[1])
    return minimum, maximum


def dot_interval(a, b):
    return plus(times(a[0], b[0]), times(a[1], b[1]))


def sqrt3_interval():
    denominator = 1 << SQRT_BITS
    numerator = math.isqrt(3*denominator*denominator)
    require(numerator*numerator < 3*denominator*denominator < (numerator+1)*(numerator+1),
            "sqrt(3) enclosure is not strict")
    return Q(numerator, denominator), Q(numerator+1, denominator)


def trig_interval(lo, hi):
    require(Q(-1) <= lo < hi <= Q(1), "angle cell outside [-1,1]")
    # sin(2 atan t) is increasing for -1<=t<=1. cos is decreasing in |t|.
    largest = max(abs(lo), abs(hi))
    smallest = Q(0) if lo <= 0 <= hi else min(abs(lo), abs(hi))
    cosine = ((1-largest*largest)/(1+largest*largest),
              (1-smallest*smallest)/(1+smallest*smallest))
    sine = (2*lo/(1+lo*lo), 2*hi/(1+hi*hi))
    return cosine, sine


def normal_intervals(lo, hi, root):
    c, s = trig_interval(lo, hi)
    h = scale(root, Q(1, 2))
    return ((c, s),
            (minus(scale(c, Q(-1, 2)), times(h, s)),
             minus(times(h, c), scale(s, Q(1, 2)))),
            (plus(scale(c, Q(-1, 2)), times(h, s)),
             minus(scale(times(h, c), Q(-1)), scale(s, Q(1, 2)))))


def point_boxes(points, root):
    return tuple((point_interval(x), plus(point_interval(y), scale(root, z)))
                 for x, y, z in points)


def supports(normals, boxes):
    result = []
    for n in normals:
        values = [dot_interval(n, p) for p in boxes]
        result.append((max(v[0] for v in values), max(v[1] for v in values)))
    return tuple(result)


def extreme_offsets(s, h, extreme):
    # Exact cancellation is done symbolically before interval evaluation.
    result = list(s)
    others = [j for j in range(3) if j != extreme]
    result[extreme] = minus(h, plus(s[others[0]], s[others[1]]))
    return tuple(result)


def vertices(normals, offsets):
    result = []
    for i, j in VERTEX_PAIRS:
        first = scale(plus(offsets[i], scale(offsets[j], Q(1, 2))), Q(4, 3))
        second = scale(plus(offsets[j], scale(offsets[i], Q(1, 2))), Q(4, 3))
        result.append(tuple(plus(times(first, normals[i][axis]),
                                 times(second, normals[j][axis])) for axis in (0, 1)))
    return tuple(result)


def cell_geometry(points_box, root, lo, hi):
    h = scale(root, Q(1, 2))
    normals = normal_intervals(lo, hi, root)
    s = supports(normals, points_box)
    no_fit = sum(v[0] for v in s) > h[1]
    return h, normals, s, no_fit


def segment_hits_disk(vertex_boxes, edge, weight, radius_squared):
    require(type(edge) in (list, tuple) and tuple(edge) in EDGES, "invalid edge")
    require(Q(0) <= weight <= Q(1), "segment weight must be convex")
    i, j = edge
    witness = tuple(plus(scale(vertex_boxes[i][axis], 1-weight),
                         scale(vertex_boxes[j][axis], weight)) for axis in (0, 1))
    norm_squared = plus(square(witness[0]), square(witness[1]))
    return norm_squared[1] < radius_squared


def verify_certificate(values, radius_squared, certificate):
    """Separate consumer: rebuild interval bounds and check every leaf and coverage.

    Returns True iff all orientations were certified. A well-formed partial
    certificate returns False. Any changed/unsupported assertion raises Rejected.
    No producer, midpoint, proposed-weight, or recursive-search function is called.
    """
    points, radius, input_sha = normalized_input(values, radius_squared)
    require(type(certificate) is dict and set(certificate) == {
        "schema", "input_sha256", "radius_squared", "sqrt3_bits", "angle_domain",
        "status", "leaves", "frontier", "diagnostics"}, "certificate keys differ")
    require(certificate["schema"] == SCHEMA, "wrong NI certificate schema")
    require(certificate["input_sha256"] == input_sha and certificate["radius_squared"] == str(radius),
            "NI certificate bound to different inputs/radius")
    require(type(certificate["sqrt3_bits"]) is int and certificate["sqrt3_bits"] == SQRT_BITS,
            "wrong sqrt(3) precision")
    require(certificate["angle_domain"] == ["-1", "1"], "wrong full angle domain")
    leaves, frontier = certificate["leaves"], certificate["frontier"]
    require(type(leaves) is list and type(frontier) is list, "cell arrays required")
    root = sqrt3_interval()
    boxes = point_boxes(points, root)
    intervals = []
    for leaf in leaves:
        require(type(leaf) is dict, "leaf must be object")
        lo, hi = fraction(leaf.get("lo")), fraction(leaf.get("hi"))
        require(Q(-1) <= lo < hi <= Q(1), "invalid leaf interval")
        intervals.append((lo, hi))
        h, normals, s, no_fit = cell_geometry(boxes, root, lo, hi)
        if leaf.get("kind") == "support":
            require(set(leaf) == {"lo", "hi", "kind"} and no_fit, "support leaf not certified")
            continue
        require(leaf.get("kind") == "three_extremes" and set(leaf) == {"lo", "hi", "kind", "witnesses"},
                "unknown NI leaf")
        witnesses = leaf["witnesses"]
        require(type(witnesses) is list and len(witnesses) == 3, "three extreme witnesses required")
        for extreme, witness in enumerate(witnesses):
            require(type(witness) is dict, "witness must be object")
            offsets = extreme_offsets(s, h, extreme)
            if witness.get("kind") == "origin_inside":
                require(set(witness) == {"kind"} and all(b[0] >= 0 for b in offsets),
                        "origin-inside witness not certified")
                continue
            require(witness.get("kind") == "segment" and set(witness) == {"kind", "edge", "weight"},
                    "unsupported disk witness")
            edge = witness["edge"]
            require(type(edge) is list and len(edge) == 2 and all(type(k) is int for k in edge)
                    and tuple(edge) in EDGES, "bad segment indices")
            weight = fraction(witness["weight"])
            require(segment_hits_disk(vertices(normals, offsets), edge, weight, radius),
                    "segment does not certify a strict open-disk hit")
    for cell in frontier:
        require(type(cell) is dict and set(cell) == {"lo", "hi", "reason"}, "malformed frontier")
        lo, hi = fraction(cell["lo"]), fraction(cell["hi"])
        require(Q(-1) <= lo < hi <= Q(1), "invalid frontier interval")
        require(cell["reason"] in {"cell_limit", "depth_limit", "cpu_limit"}, "unknown frontier reason")
        intervals.append((lo, hi))
    require(bool(intervals), "empty angular coverage")
    intervals.sort()
    require(intervals[0][0] == -1 and intervals[-1][1] == 1, "angle endpoints omitted")
    require(all(previous[1] == current[0] for previous, current in zip(intervals, intervals[1:])),
            "angle cells overlap or omit an interval")
    proved = not frontier
    require(certificate["status"] == ("PROVED_NI_INFEASIBLE" if proved else "UNKNOWN"),
            "status contradicts unresolved angle cells")
    return proved


