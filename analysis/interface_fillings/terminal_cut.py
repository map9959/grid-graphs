"""Extract the actual one-edge terminal condition in the prepared control.

python3 -m analysis.interface_fillings.terminal_cut INPUT.json OUTPUT.json
"""

import argparse
import hashlib
import json
from collections import deque
from pathlib import Path

from .audit import rank
from .replacements_audit import labels


def path_between(labels_, edges, start, end):
    adjacency = [[] for _ in labels_]
    for v, w in edges:
        if labels_[v] or labels_[w]:
            adjacency[v].append(w)
            adjacency[w].append(v)
    parents = {start: None}
    queue = deque([start])
    while queue:
        v = queue.popleft()
        if v == end:
            path = []
            while v is not None:
                path.append(v)
                v = parents[v]
            return path[::-1]
        for w in adjacency[v]:
            if w not in parents:
                parents[w] = v
                queue.append(w)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    prepared = next(b for b in data["boards"] if b["name"] == "prepared76")
    original = labels(prepared["original"]["rows"])
    case = next(c for c in prepared["cases"] if c["name"] == "control_core_boundary")
    final = labels(case["result"]["best_rows"])
    core = final.copy()
    core[10] = False
    edges = [(y*14+x, yy*14+xx) for y in range(14) for x in range(14)
             for xx, yy in [(x+1, y), (x, y+1)] if xx < 14 and yy < 14]
    for state in (original, core, final):
        assert rank(state, edges) == 0
    assert sum(original) == sum(core) == 76 and sum(final) == 77
    assert original[9] and original[11] and not original[10] and not original[24]
    assert all(core[v] == original[v] for v in (9, 10, 11, 24))
    forced = lambda state: {(v, w) for v, w in edges if state[v] or state[w]}
    assert forced(final) - forced(core) == {(10, 24)}
    assert not (forced(core) - forced(final))
    before_path = path_between(original, edges, 10, 24)
    assert before_path is not None
    assert path_between(core, edges, 10, 24) is None
    result = {
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "scope": "literal actual-tree path certificate for one prepared control",
        "terminal": 10, "new_edge": [10, 24],
        "original_unique_path": before_path,
        "original_path_length": len(before_path) - 1,
        "core_deleted": [v for v in range(196) if original[v] and not core[v]],
        "core_added": [v for v in range(196) if core[v] and not original[v]],
        "forced_components_before": 196-len(forced(original)),
        "forced_components_after_core": 196-len(forced(core)),
        "forced_components_final": 196-len(forced(final)),
        "core_rows": ["".join("." if f else "U" for f in core[y*14:(y+1)*14]) for y in range(14)],
    }
    print(json.dumps({k: v for k, v in result.items() if k != "core_rows"}))
    with args.output.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
