"""Negative controls for the finite-configuration certificate reader."""
import hashlib
import shutil
import tempfile
import unittest
from pathlib import Path

import intervals
import verify


class CertificateControls(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.data = Path(self.scratch.name) / 'data'
        shutil.copytree(verify.DATA, self.data)

    def read(self, name):
        return intervals.load(self.data / name)

    def write(self, name, value):
        (self.data / name).write_bytes(intervals.canonical(value))

    def test_changed_clearance_even_after_tree_is_rebound(self):
        packet = self.read('packet.json')
        packet['ni_radius_squared'] = '243/10000'
        tree = self.read('tree.json')
        tree['packet_sha256'] = hashlib.sha256(intervals.canonical(packet)).hexdigest()
        self.write('packet.json', packet)
        self.write('tree.json', tree)
        with self.assertRaisesRegex(ValueError, 'wrong squared distance'):
            verify.with_distance(self.data)

    def test_omitted_input_point(self):
        points = self.read('points.json')
        points['queries'].remove(165)
        del points['points']['165']
        self.write('points.json', points)
        for check in (verify.with_distance, verify.without_distance):
            with self.subTest(check=check.__name__):
                with self.assertRaisesRegex(ValueError, 'wrong number'):
                    check(self.data)

    def test_removed_owner(self):
        tree = self.read('tree.json')
        del tree['nodes'][0]['cases']['5']
        self.write('tree.json', tree)
        with self.assertRaisesRegex(ValueError, 'missing feasible owner'):
            verify.with_distance(self.data)

    def test_degenerate_unit_claim(self):
        vertices = self.read('vertices.json')
        vertices['T5'][0] = vertices['T5'][1]
        self.write('vertices.json', vertices)
        with self.assertRaisesRegex(ValueError, 'not exactly one'):
            verify.without_distance(self.data)

    def test_replaced_interval_leaves_with_same_count(self):
        cert = self.read('interval-402.json')
        cert['leaves'][0] = cert['leaves'][1]
        self.write('interval-402.json', cert)
        with self.assertRaisesRegex(ValueError, 'angle (cells|endpoints)'):
            verify.with_distance(self.data)


if __name__ == '__main__':
    unittest.main()
