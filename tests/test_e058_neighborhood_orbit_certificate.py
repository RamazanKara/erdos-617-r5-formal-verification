from __future__ import annotations

import itertools
import tempfile
import unittest
from pathlib import Path

from repro.generate_e058_neighborhood_orbit_certificate import (
    CATALOG,
    relabel_mask,
    render_source,
    witnesses,
)


class NeighborhoodOrbitCertificateTests(unittest.TestCase):
    def test_complete_exact_witness_table(self) -> None:
        records = witnesses()
        self.assertEqual(len(records), 1024)
        self.assertEqual(len(CATALOG), 26)
        for mask, (branch, permutation) in enumerate(records):
            self.assertEqual(tuple(sorted(permutation)), tuple(range(5)))
            if mask.bit_count() <= 6:
                self.assertEqual(relabel_mask(mask, permutation), CATALOG[branch])

    def test_first_lexicographic_minimizer(self) -> None:
        records = witnesses()
        permutations = tuple(itertools.permutations(range(5)))
        for mask in range(1024):
            if mask.bit_count() > 6:
                continue
            branch, permutation = records[mask]
            expected = min(
                (relabel_mask(mask, candidate), candidate)
                for candidate in permutations
            )
            self.assertEqual((CATALOG[branch], permutation), expected)

    def test_render_is_deterministic(self) -> None:
        records = witnesses()
        first = render_source(records)
        second = render_source(witnesses())
        self.assertEqual(first, second)
        self.assertIn("theorem r5NeighborhoodOrbitWitness_correct", first)
        self.assertEqual(first.count("\n  | "), 1025)
        with tempfile.TemporaryDirectory(
            prefix="erdos617-orbit-render-"
        ) as directory:
            path = Path(directory) / "certificate.lean"
            path.write_text(first, encoding="utf-8", newline="\n")
            self.assertEqual(path.read_text(encoding="utf-8"), second)


if __name__ == "__main__":
    unittest.main(verbosity=2)
