"""Replay one finite instance. Usage: python3 verify.py with-distance|without-distance"""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import geometry as geom
import intervals

DATA = Path(__file__).resolve().parent / 'data'
RADIUS_SQUARED = 3 * Q(81, 200)**2
ROLE_NAMES = ['T0', 'T1', 'T2', 'T3', 'T4', 'T5', 'C']
ZERO = (Q(0), Q(0))


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def finite_point(row):
    x, y, z = map(Q, row)
    return (x, Q(0)), (y, z)


def read_problem(data):
    obj = intervals.load(data / 'points.json')
    raw = {int(i): row for i, row in obj['points'].items()}
    points = {i: finite_point(row) for i, row in raw.items()}
    mandatory, queries = obj['mandatory'], obj['queries']
    require([len(row) for row in mandatory] == [3]*6 + [21], 'wrong prescribed roles')
    owners = [i for row in mandatory for i in row]
    require(len(queries) == 66 and len(points) == len(set(points.values())) == 105,
            'wrong number of distinct locations')
    require(set(queries + owners) == set(points), 'point IDs or assigned/free partition differ')
    for (x, _), y in points.values():
        for sign in [-1, 1]:
            signed_y = geom.scale(sign, y)
            for cap in [Q(1, 2), 1 - abs(x)]:
                require(geom.sg(geom.sub(signed_y, (0, cap))) <= 0, 'point outside unit hexagon')
    return raw, points, mandatory, queries


def check_triangle(triangle):
    require(len(triangle) == 3, 'three vertices required')
    for i, v in enumerate(triangle):
        edge = geom.vd(v, triangle[i-1])
        require(geom.dot(edge, edge) == (1, 0), 'triangle side is not exactly one')


def contains(triangle, point):
    signs = []
    for i, vertex in enumerate(triangle):
        edge = geom.vd(vertex, triangle[i-1])
        signs.append(geom.sg(geom.cross(edge, geom.vd(point, triangle[i-1]))))
    return min(signs) >= 0 or max(signs) <= 0


def without_distance(data):
    _, points, mandatory, queries = read_problem(data)
    vertex_rows = intervals.load(data / 'vertices.json')
    require(set(vertex_rows) == set(ROLE_NAMES), 'wrong triangle labels')
    triangles = []
    for name, ids in zip(ROLE_NAMES, mandatory):
        triangle = [tuple(tuple(map(Q, axis)) for axis in v) for v in vertex_rows[name]]
        check_triangle(triangle)
        require(all(contains(triangle, points[i]) for i in ids), 'missed prescribed point')
        triangles.append(triangle)
    for i in queries:
        require(any(contains(t, points[i]) for t in triangles), f'uncovered free point {i}')

    # The projection p lies in T5. T5 is on the far side of its perpendicular
    # supporting line through p, so the infimum distance is exactly |p|.
    foot = ((Q(27, 200), Q(0)), (Q(0), Q(-9, 200)))
    t5 = triangles[5]
    require(contains(t5, foot), 'T5 does not contain the foot')
    require(all(geom.sg(geom.dot(foot, geom.vd(v, foot))) >= 0 for v in t5),
            'wrong supporting line for T5')
    squared = geom.dot(foot, foot)
    require(squared == (Q(243, 10000), 0) and squared[0] < RADIUS_SQUARED,
            'incorrect clearance for witness')
    return 'POSSIBLE: all 21 unit sides, 39 prescribed and 66 free points checked; d(0,T5)^2 = 243/10000.'


def center_cannot_cover(point, prescribed):
    # Four axial points force a diamond, which contains the disk of radius 1/21.
    r, rho = Q(1411, 20000), Q(1, 21)
    axial = {((a*r, Q(0)), (b*r, Q(0))) for a, b in [(1, 0), (-1, 0), (0, 1), (0, -1)]}
    require(axial <= prescribed and 2*rho**2 <= r**2, 'inscribed disk not justified')
    # See README: the largest squared distance is at most 1-2 sqrt(3) rho+4 rho^2.
    require(Q(12, 7)**2 < 3 and rho**2 < Q(1, 12), 'invalid radical or inradius bound')
    upper = 1 - 2*Q(12, 7)*rho + 4*rho**2
    return geom.sg(geom.sub(geom.dot(point, point), (upper, 0))) > 0


def verify_tree(raw, points, mandatory, queries, packet, tree, interval_proof):
    require(Q(packet['ni_radius_squared']) == RADIUS_SQUARED, 'wrong squared distance')
    digest = hashlib.sha256(intervals.canonical(packet)).hexdigest()
    require(tree['packet_sha256'] == digest, 'tree and source packet differ')
    seed = packet['seed_packet']
    require(seed['mandatory'] == mandatory, 'prescribed role list differs from source packet')
    source_rows = seed['points'] + tree['dynamic_points']
    require(all(source_rows[i]['xyz'] == row for i, row in raw.items()), 'point coordinates differ')
    require(not tree['frontier'], 'tree has an open frontier')

    facts, nodes = tree['facts'], tree['nodes']
    seen_nodes, seen_facts, seen_points, omitted = set(), set(), set(), set()
    center = {points[i] for i in mandatory[6]}
    all_roles = set(map(str, range(7)))
    query_ids = set(queries)
    interval_facts = []
    stack = [(tree['root'], {})]
    while stack:
        ref, assigned = stack.pop()
        require(isinstance(ref, dict) and len(ref) == 1, 'invalid reference')
        kind, idx = next(iter(ref.items()))
        require(type(idx) is int and idx >= 0, 'negative or noninteger index')
        if kind == 'node':
            require(idx < len(nodes) and idx not in seen_nodes, 'invalid, cyclic or reused node')
            seen_nodes.add(idx)
            current = nodes[idx]
            point, cases = current['g'], current['cases']
            require(type(point) is int and point in query_ids and point not in assigned,
                    'invalid point query on this path')
            seen_points.add(point)
            if set(cases) != all_roles:
                require(set(cases) == all_roles - {'6'} and center_cannot_cover(points[point], center),
                        'missing feasible owner')
                omitted.add(point)
            for role, child in cases.items():
                child_assignment = assigned.copy()
                child_assignment[point] = int(role)
                stack.append((child, child_assignment))
        else:
            require(kind == 'fact' and idx < len(facts), 'nonfact leaf')
            fact = facts[idx]
            role, ids, code = fact['role'], fact['points'], fact['backend_code']
            require(type(role) is int and 0 <= role <= 6, 'invalid role')
            require(ids == sorted(set(ids)) and all(assigned.get(i) == role for i in ids),
                    'geometric fact does not belong to this path')
            if idx in seen_facts:
                continue
            seen_facts.add(idx)
            require(code != 3 or role == 5, 'clearance imposed on wrong triangle')
            values = [raw[i] for i in sorted(set(ids) | set(mandatory[role]))]
            if geom.prove(values, code, RADIUS_SQUARED) is None:
                require(code == 3 and role == 5 and
                        intervals.verify_certificate(values, RADIUS_SQUARED, interval_proof),
                        'no exact certificate for geometric fact')
                interval_facts.append(idx)
    require(len(seen_nodes) == len(nodes) and len(seen_facts) == len(facts),
            'unused tree nodes or facts')
    require(query_ids == seen_points, 'free point list and actual tree queries differ')
    require(len(nodes) == 149 and len(facts) == 468 and sorted(interval_facts) == [402]
            and omitted == {165}, 'unexpected band/certificate scope')
    return 'IMPOSSIBLE: 149 nodes, 468 geometric facts, 82 orientation intervals for fact 402, all 66 queries covered by the branching argument.'


def with_distance(data):
    raw, points, mandatory, queries = read_problem(data)
    proof = intervals.load(data / 'interval-402.json')
    require(len(proof['leaves']) == 82, 'wrong interval count')
    return verify_tree(raw, points, mandatory, queries, intervals.load(data / 'packet.json'),
                       intervals.load(data / 'tree.json'), proof)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case', choices=['without-distance', 'with-distance'])
    args = parser.parse_args()
    print((without_distance if args.case == 'without-distance' else with_distance)(DATA))


if __name__ == '__main__':
    main()
