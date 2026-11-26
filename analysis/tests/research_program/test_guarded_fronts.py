import unittest

from analysis.research_program.guarded_fronts import exchange, grid_edges, ledger, rootless14, rooted14, rooted15


class GuardedFrontTests(unittest.TestCase):
    def test_guarded_exchange_in_connected_and_disconnected_roots(self):
        for n, state, selected in [(14, rooted14(), [7]), (14, rootless14(), [7]),
                                    (15, rooted15(), [4,7])]:
            before = ledger(state, n, grid_edges(n))
            after = ledger(exchange(state, n, selected), n, grid_edges(n))
            t = len(selected)
            self.assertEqual([after[k]-before[k] for k in ("f","r","b","c","z")], [0,t,t,-2*t,-2*t])


if __name__ == "__main__":
    unittest.main()
