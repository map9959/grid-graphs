from __future__ import annotations

import itertools
import unittest

from forced_forest_favorable_side import (
    direct_counts,
    find_counterexample,
    first_monitor_state,
    monitor_transition,
    terminal_counts,
)
from forced_forest_row_grammar import is_forced_forest


class FavorableSideMonitorTests(unittest.TestCase):
    def test_product_monitor_matches_brute_force_through_n4(self) -> None:
        for n in range(1, 5):
            brute_counterexample = None
            brute_valid = 0
            monitor_terminal = {}
            for flat in range(1 << (n * n)):
                rows = tuple((flat >> (row * n)) & ((1 << n) - 1) for row in range(n))
                if not is_forced_forest(n, list(rows)):
                    continue
                brute_valid += 1
                sides, c_f, c_h = direct_counts(n, rows)
                state = first_monitor_state(n, rows[0])
                self.assertIsNotNone(state)
                for mask in rows[1:]:
                    state = monitor_transition(n, state, mask)  # type: ignore[arg-type]
                    self.assertIsNotNone(state)
                self.assertEqual(terminal_counts(n, state), (sides, c_f, c_h))  # type: ignore[arg-type]
                monitor_terminal.setdefault(state, rows)
                if min(sides) > c_f + c_h - 2 and brute_counterexample is None:
                    brute_counterexample = rows

            found, census = find_counterexample(n)
            self.assertEqual(found is not None, brute_counterexample is not None)
            self.assertEqual(census["terminal_states"], len(monitor_terminal))
            self.assertLessEqual(census["terminal_states"], brute_valid)


if __name__ == "__main__":
    unittest.main()
