"""Exact point, hull, support, and disk witnesses in Q(sqrt(3)).

A scalar (a, b) represents a + b*sqrt(3). A planar point has two such
coordinates. The geometric predicates clear a common positive denominator D
from all coordinates and keep track of it in their inequalities.
"""
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations
import math


def sg(z):
    """Compare a + b*sqrt(3) with zero without approximating the radical."""
    a, b = z
    if a == 0:
        return (b > 0) - (b < 0)
    sign_a = (a > 0) - (a < 0)
    if b == 0 or (a > 0) == (b > 0):
        return sign_a
    difference = a * a - 3 * b * b
    return sign_a * ((difference > 0) - (difference < 0))


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def neg(a):
    return (-a[0], -a[1])


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    return (a[0] * b[0] + 3 * a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def scale(k, a):
    return (k * a[0], k * a[1])


def sq(a):
    return mul(a, a)


def rt(a):
    """Multiply by sqrt(3)."""
    return (3 * a[1], a[0])


def vd(a, b):
    """Vector difference between two planar points."""
    return (sub(a[0], b[0]), sub(a[1], b[1]))


def dot(a, b):
    return add(mul(a[0], b[0]), mul(a[1], b[1]))


def cross(a, b):
    return sub(mul(a[0], b[1]), mul(a[1], b[0]))


def decode(values):
    if (
        not isinstance(values, (list, tuple))
        or not values
        or any(
            not isinstance(row, (list, tuple))
            or len(row) != 3
            or any(type(entry) is not str for entry in row)
            for row in values
        )
    ):
        raise ValueError('nonempty exact string-triple point list required')
    rows = [tuple(map(Fraction, row)) for row in values]
    denominator = math.lcm(*(entry.denominator for row in rows for entry in row))
    points = [
        ((int(x * denominator), 0), (int(y * denominator), int(z * denominator)))
        for x, y, z in rows
    ]
    return points, denominator


def compare(a, b):
    """Lexicographic order on two exact planar points."""
    x_order = sg(sub(a[0], b[0]))
    return x_order or sg(sub(a[1], b[1]))


def hull(P):
    points = sorted(set(P), key=cmp_to_key(compare))
    if len(points) <= 1:
        return points

    def chain(ordered_points):
        result = []
        for point in ordered_points:
            while len(result) > 1:
                previous_edge = vd(result[-1], result[-2])
                next_edge = vd(point, result[-1])
                if sg(cross(previous_edge, next_edge)) > 0:
                    break
                result.pop()
            result.append(point)
        return result

    return chain(points)[:-1] + chain(reversed(points))[:-1]


def diameter_witness(P, D):
    for i, j in combinations(range(len(P)), 2):
        edge = vd(P[i], P[j])
        excess = sub(dot(edge, edge), (D * D, 0))
        if sg(excess) > 0:
            return {
                'pair': [i, j],
                'excess_integer_ring': excess,
                'denominator_squared': D * D,
            }
    return None


def support_events(P, D):
    boundary = hull(P)
    if len(boundary) < 2:
        return None
    events = []
    for i, start in enumerate(boundary):
        end = boundary[(i + 1) % len(boundary)]
        edge = vd(end, start)
        nx, ny = edge[1], neg(edge[0])

        # Twice the outer edge normal and its rotations through 120 and 240 degrees.
        first = (scale(2, nx), scale(2, ny))
        second = (sub(neg(nx), rt(ny)), sub(rt(nx), ny))
        third = (neg(add(first[0], second[0])), neg(add(first[1], second[1])))

        support_sum = (0, 0)
        supporting_vertices = []
        for direction in (first, second, third):
            best_index = 0
            best_value = dot(direction, boundary[0])
            for index, point in enumerate(boundary[1:], start=1):
                value = dot(direction, point)
                if sg(sub(value, best_value)) > 0:
                    best_value = value
                    best_index = index
            support_sum = add(support_sum, best_value)
            supporting_vertices.append(best_index)

        if sg(support_sum) < 0:
            raise ValueError('support sum must be nonnegative')
        # Undo the common scales in height * |normal| before squaring.
        gap = sub(sq(support_sum), scale(3 * D * D, dot(edge, edge)))
        if sg(gap) <= 0:
            return None
        events.append({
            'edge': i,
            'supports': supporting_vertices,
            'strict_squared_gap': gap,
        })
    return {'hull': boundary, 'denominator': D, 'all_events': events}


def disk_witness(P, D, R):
    """Find a required point or segment strictly inside the excluded disk.

    R is the squared radius. Every closed triangle containing two required
    points contains the entire segment joining them.
    """
    numerator, denominator = R.numerator, R.denominator

    def radial_gap(point):
        return sub(scale(denominator, dot(point, point)), (numerator * D * D, 0))

    for i, point in enumerate(P):
        gap = radial_gap(point)
        if sg(gap) < 0:
            return {'point': i, 'strict_scaled_radial_gap': gap}

    for i, j in combinations(range(len(P)), 2):
        start = P[i]
        edge = vd(P[j], start)
        norm_squared = dot(edge, edge)
        projection = neg(dot(start, edge))
        # The perpendicular foot lies strictly between the segment endpoints.
        if sg(projection) <= 0 or sg(sub(norm_squared, projection)) <= 0:
            continue
        gap = sub(mul(radial_gap(start), norm_squared), scale(denominator, sq(projection)))
        if sg(gap) < 0:
            return {
                'segment': [i, j],
                'strict_scaled_radial_gap': gap,
                'projection': projection,
                'segment_norm_squared': norm_squared,
            }
    return None


def prove(values, code, R):
    if type(code) is not int or code not in (1, 2, 3):
        raise ValueError('unsupported claimed code')
    if code == 3 and (type(R) is not Fraction or R <= 0):
        raise ValueError('positive exact squared radius required')
    points, denominator = decode(values)
    if code == 1:
        return diameter_witness(points, denominator)
    if code == 2:
        return support_events(points, denominator)
    return disk_witness(points, denominator, R)
