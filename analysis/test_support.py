from __future__ import annotations

import os
import unittest


slow_test = unittest.skipUnless(
    os.environ.get("GRID_GRAPHS_RUN_SLOW_TESTS") == "1",
    "set GRID_GRAPHS_RUN_SLOW_TESTS=1 to run slow exact-search/integration tests",
)
