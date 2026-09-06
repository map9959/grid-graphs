from __future__ import annotations

import json
import unittest


from analysis.residue_certificates.residue_two_local_motif_grammar import maximum_face_cut_open_width
from analysis.tiles.tile_grammar import advance_row, initial_state, row_mask
from analysis._paths import ANALYSIS_ROOT
from analysis.tests._support import migrated_artifact


HERE = ANALYSIS_ROOT
RESULT = HERE / "residue_two_n11_face_cut_defect_result.json"


class ResidueTwoN11FaceCutDefectResultTests(unittest.TestCase):
    def test_exact_result_and_positive_witness(self) -> None:
        result = migrated_artifact(json.loads(RESULT.read_text()))
        query = result["first_defect_query"]
        self.assertEqual(query["minimum_codec_valid_u"], 72)
        self.assertEqual(query["minimum_codec_defective_u"], 73)
        self.assertEqual(query["defect_gap"], 3)

        rows = (HERE.parent / query["witness"]).read_text().splitlines()
        self.assertEqual(len(rows), 11)
        self.assertEqual(sum(row.count("U") for row in rows), 73)
        state = initial_state(11)
        first_defect = None
        maximum = 0
        for row_number, row in enumerate(rows, 1):
            state = advance_row(state, row_mask(row))
            self.assertIsNotNone(state)
            assert state is not None
            width = maximum_face_cut_open_width(state)
            maximum = max(maximum, width)
            if first_defect is None and width > 1:
                first_defect = row_number
        self.assertEqual(state.partition, (0,))
        self.assertEqual(3 * state.u_cost - 2 * 10**2 - 11, 8)
        self.assertEqual(first_defect, query["first_defect_row"])
        self.assertEqual(maximum, query["maximum_face_cut_width"])

    def test_curvature_five_channel_has_no_defect(self) -> None:
        result = migrated_artifact(json.loads(RESULT.read_text()))
        query = result["curvature_five_query"]
        self.assertEqual(query["minimum_codec_valid_u"], 72)
        self.assertIsNone(query["minimum_codec_defective_u"])
        self.assertFalse(result["scope"]["symmetry_reduction"])
        self.assertFalse(result["scope"]["beam_pruning"])


if __name__ == "__main__":
    unittest.main()
