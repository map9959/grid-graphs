#!/usr/bin/env python3
"""Find a sparse candidate formula for the pooled frontier potential.

HiGHS is used only to propose coefficients. Every proposed coefficient is
rationalized and every source transition is then checked with exact Fraction
arithmetic before a candidate is reported.
"""

from __future__ import annotations

import argparse
import json
import math
import shutil
import subprocess
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from analysis.bounds.proof_oriented_identities import (
    _constraint_weight,
    _feature_id,
    export_complete_tile_row_source,
    frontier_feature_signature,
    synthesize_difference_potentials,
)
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
DEFAULT_HIGHS = Path(shutil.which("highs") or "/tmp/opencode/bin/highs")
DEFAULT_WORK = Path("/tmp/opencode")
FIELDS = (
    "phase",
    "mode",
    "u",
    "left_u",
    "right_u",
    "out",
    "debt",
    "left_out",
    "right_out",
    "runs",
)
MODES = ("top", "bulk", "bottom", "terminal")
DESIRED_TERMINALS = {0: 4, 1: 2, 2: 5}
ACTIVE_BASIS = "hinges"
ACTIVE_FEATURE_LEVEL = "runs"


@dataclass(frozen=True)
class DecisionNode:
    value: Fraction | None = None
    field: str | None = None
    threshold: int | str | None = None
    equality: bool = False
    left: "DecisionNode | None" = None
    right: "DecisionNode | None" = None


def _features(n: int, metadata: dict) -> dict[str, int | str]:
    signature = frontier_feature_signature(n, metadata, ACTIVE_FEATURE_LEVEL)
    fields = FIELDS + (("out_intervals",) if ACTIVE_FEATURE_LEVEL == "out" else ())
    features = dict(zip(fields, signature, strict=True))
    active_faces = 0 if features["mode"] in ("top", "terminal") else n - 1
    features["frontier_faces"] = active_faces
    features["unattached_faces"] = active_faces - int(features["out"])
    return features


def _base_terms(feature: dict[str, int | str]) -> dict[str, int]:
    u = int(feature["u"])
    runs = int(feature["runs"])
    out = int(feature["out"])
    debt = int(feature["debt"])
    left_u = int(feature["left_u"])
    right_u = int(feature["right_u"])
    left_out = int(feature["left_out"])
    right_out = int(feature["right_out"])
    frontier_faces = int(feature["frontier_faces"])
    unattached_faces = int(feature["unattached_faces"])
    out_intervals = int(feature.get("out_intervals", 0))
    terms = {
        "u": u,
        "runs": runs,
        "out": out,
        "debt": debt,
        "left_u": left_u,
        "right_u": right_u,
        "left_out": left_out,
        "right_out": right_out,
        "row_curvature": u + 2 * runs,
        "run_adjacencies": u - runs,
        "internal_run_ends": 2 * runs - left_u - right_u,
        "fragmentation": max(runs - 1, 0),
        "short_runs": max(2 * runs - u, 0),
        "dense_runs": max(u - 2 * runs, 0),
        "missing_out_sides": 2 - left_out - right_out,
        "endpoint_debt": max(left_u - left_out, 0) + max(right_u - right_out, 0),
        "component_out_debt": max(debt - out, 0),
        "run_out_debt": max(runs - out, 0),
        "port_debt": max(debt - left_out - right_out, 0),
        "attachment_debt": max(runs + debt - out - left_out - right_out, 0),
        "frontier_faces": frontier_faces,
        "unattached_faces": unattached_faces,
        "face_component_excess": max(unattached_faces - debt, 0),
        "component_face_deficit": max(debt - unattached_faces, 0),
        "out_intervals": out_intervals,
    }
    if ACTIVE_BASIS == "linear":
        return terms
    hinge_inputs = {
        "u": u,
        "runs": runs,
        "out": out,
        "debt": debt,
        "unattached_faces": unattached_faces,
        "u_minus_2runs": u - 2 * runs,
        "2runs_minus_u": 2 * runs - u,
        "runs_minus_out": runs - out,
        "debt_minus_out": debt - out,
        "runs_debt_minus_out": runs + debt - out,
        "runs_debt_minus_coverage": runs + debt - out - left_out - right_out,
        "unattached_minus_runs": unattached_faces - runs,
        "unattached_minus_debt": unattached_faces - debt,
    }
    for name, value in hinge_inputs.items():
        for threshold in range(-2, 7):
            terms[f"hinge:{name}:{threshold}"] = max(value - threshold, 0)
    if ACTIVE_BASIS == "hinges":
        return terms
    predicate_values = {
        "u": u,
        "runs": runs,
        "out": out,
        "debt": debt,
        "unattached": unattached_faces,
    }
    polynomial_values = {
        **predicate_values,
        "left_u": left_u,
        "right_u": right_u,
        "left_out": left_out,
        "right_out": right_out,
    }
    polynomial_names = sorted(polynomial_values)
    for left_index, left in enumerate(polynomial_names):
        for right in polynomial_names[left_index:]:
            terms[f"product:{left}:{right}"] = (
                polynomial_values[left] * polynomial_values[right]
            )
    endpoint_pattern = left_u | (right_u << 1) | (left_out << 2) | (right_out << 3)
    for pattern in range(16):
        terms[f"endpoint_pattern:{pattern}"] = int(endpoint_pattern == pattern)
    for name, value in predicate_values.items():
        for threshold in range(0, 7):
            terms[f"at_most:{name}:{threshold}"] = int(value <= threshold)
    for left, right in (
        ("u", "runs"),
        ("runs", "out"),
        ("runs", "debt"),
        ("debt", "out"),
        ("unattached", "debt"),
        ("unattached", "runs"),
    ):
        for left_threshold in range(0, 7):
            for right_threshold in range(0, 7):
                terms[
                    f"rectangle:{left}:{left_threshold}:{right}:{right_threshold}"
                ] = int(
                    predicate_values[left] <= left_threshold
                    and predicate_values[right] <= right_threshold
                )
    return terms


def formula_terms(feature: dict[str, int | str]) -> dict[str, int]:
    """Return the overcomplete, interpretable candidate basis."""
    phase = int(feature["phase"])
    mode = str(feature["mode"])
    if ACTIVE_BASIS == "lookup":
        fields = FIELDS + (("out_intervals",) if ACTIVE_FEATURE_LEVEL == "out" else ())
        lookup_key = json.dumps([feature[field] for field in fields], separators=(",", ":"))
        return {f"lookup:{lookup_key}": 1}
    base = _base_terms(feature)
    terms = {f"intercept:p{phase}:{mode}": 1}
    for name, value in base.items():
        terms[f"piece:p{phase}:{mode}:{name}"] = value
    return terms


def _linear_difference(outgoing: dict[str, int], incoming: dict[str, int]) -> dict[str, int]:
    names = outgoing.keys() | incoming.keys()
    return {
        name: outgoing.get(name, 0) - incoming.get(name, 0)
        for name in names
        if outgoing.get(name, 0) != incoming.get(name, 0)
    }


def build_constraints(widths: tuple[int, ...]) -> tuple[list[str], list[tuple[dict[str, int], str, int]]]:
    names: set[str] = set()
    constraints: list[tuple[dict[str, int], str, int]] = []
    anchors = []
    for n in widths:
        source = export_complete_tile_row_source(n, 1)
        features = {
            state["id"]: _features(n, state["metadata"])
            for state in source["states"]
        }
        terms = {state_id: formula_terms(value) for state_id, value in features.items()}
        names.update(name for values in terms.values() for name in values)
        anchors.append(terms[source["initial_id"]])
        for transition in source["transitions"]:
            difference = _linear_difference(terms[transition["out"]], terms[transition["in"]])
            rhs = 3 * transition["dU"] - 2 * transition["dRank"] - 1
            constraints.append((difference, "<=", rhs))
        for state in source["states"]:
            if state["metadata"]["row_index"] != n:
                continue
            constraints.append((terms[state["id"]], ">=", DESIRED_TERMINALS[n % 3]))
    for anchor in anchors:
        constraints.append((anchor, "=", 0))
    return sorted(names), constraints


def build_shortest_potential_table(
    widths: tuple[int, ...],
) -> list[tuple[dict[str, int | str], Fraction]]:
    all_features: dict[str, dict[str, int | str]] = {}
    pooled = {}
    anchor = None
    for n in widths:
        source = export_complete_tile_row_source(n, 1)
        features = {
            state["id"]: _features(n, state["metadata"])
            for state in source["states"]
        }
        fields = FIELDS + (("out_intervals",) if ACTIVE_FEATURE_LEVEL == "out" else ())
        ids = {
            state_id: _feature_id(tuple(value[field] for field in fields))
            for state_id, value in features.items()
        }
        all_features.update((ids[state_id], value) for state_id, value in features.items())
        initial = ids[source["initial_id"]]
        if anchor is None:
            anchor = initial
        elif anchor != initial:
            raise AssertionError("training widths do not share an initial feature")
        for transition in source["transitions"]:
            record = {**transition, "in": ids[transition["in"]], "out": ids[transition["out"]]}
            pair = (record["in"], record["out"])
            if pair not in pooled or _constraint_weight(record) < _constraint_weight(pooled[pair]):
                pooled[pair] = record
    assert anchor is not None
    potentials = synthesize_difference_potentials(
        sorted(all_features), list(pooled.values()), anchor
    )
    return [(feature, potentials[state_id]) for state_id, feature in all_features.items()]


def _tree_coordinates(feature: dict[str, int | str]) -> dict[str, int | str]:
    return {**feature, **{f"derived:{key}": value for key, value in _base_terms(feature).items()}}


def _entropy(samples: list[tuple[dict[str, int | str], Fraction]]) -> float:
    counts = {}
    for _, value in samples:
        counts[value] = counts.get(value, 0) + 1
    total = len(samples)
    return -sum((count / total) * math.log2(count / total) for count in counts.values())


def _candidate_splits(samples: list[tuple[dict[str, int | str], Fraction]]):
    fields = sorted(samples[0][0])
    for field in fields:
        values = sorted({feature[field] for feature, _ in samples}, key=str)
        if len(values) < 2:
            continue
        if isinstance(values[0], str):
            for value in values[:-1]:
                yield field, value, True
        else:
            numeric = sorted(int(value) for value in values)
            for threshold in numeric[:-1]:
                yield field, threshold, False


def _partition_samples(samples, field, threshold, equality):
    if equality:
        left = [sample for sample in samples if sample[0][field] == threshold]
    else:
        left = [sample for sample in samples if int(sample[0][field]) <= int(threshold)]
    left_ids = {id(sample) for sample in left}
    right = [sample for sample in samples if id(sample) not in left_ids]
    return left, right


def build_decision_tree(
    samples: list[tuple[dict[str, int | str], Fraction]]
) -> DecisionNode:
    values = {value for _, value in samples}
    if len(values) == 1:
        return DecisionNode(value=values.pop())
    best = None
    for field, threshold, equality in _candidate_splits(samples):
        left, right = _partition_samples(samples, field, threshold, equality)
        if not left or not right:
            continue
        score = len(left) * _entropy(left) + len(right) * _entropy(right)
        candidate = (score, field, str(threshold), threshold, equality, left, right)
        if best is None or candidate[:3] < best[:3]:
            best = candidate
    if best is None:
        raise ValueError(f"no decision split separates {len(values)} potential values")
    _, field, _, threshold, equality, left, right = best
    return DecisionNode(
        field=field,
        threshold=threshold,
        equality=equality,
        left=build_decision_tree(left),
        right=build_decision_tree(right),
    )


def _tree_stats(tree: DecisionNode) -> tuple[int, int]:
    if tree.value is not None:
        return 1, 0
    assert tree.left is not None and tree.right is not None
    left_leaves, left_depth = _tree_stats(tree.left)
    right_leaves, right_depth = _tree_stats(tree.right)
    return left_leaves + right_leaves, 1 + max(left_depth, right_depth)


def evaluate_decision_tree(tree: DecisionNode, feature: dict[str, int | str]) -> Fraction:
    coordinates = _tree_coordinates(feature)
    node = tree
    while node.value is None:
        assert node.field is not None and node.threshold is not None
        observed = coordinates[node.field]
        go_left = observed == node.threshold if node.equality else int(observed) <= int(node.threshold)
        child = node.left if go_left else node.right
        if child is None:
            raise AssertionError("decision tree has a missing child")
        node = child
    return node.value


def validate_tree_width(tree: DecisionNode, n: int) -> dict[str, object]:
    from analysis.tiles.tile_grammar import advance_row, initial_state

    representatives = {(0, 0, (0,)): initial_state(n)}
    layer_counts = [1]
    attempted = accepted = tight = 0
    minimum_slack: Fraction | None = None
    for _ in range(n):
        children = {}
        for incoming in representatives.values():
            incoming_metadata = {
                "row_index": incoming.row_index,
                "previous_u_mask": incoming.previous_u_mask,
                "partition": incoming.partition,
            }
            incoming_value = evaluate_decision_tree(tree, _features(n, incoming_metadata))
            for mask in range(1 << n):
                attempted += 1
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                accepted += 1
                outgoing_metadata = {
                    "row_index": outgoing.row_index,
                    "previous_u_mask": outgoing.previous_u_mask,
                    "partition": outgoing.partition,
                }
                outgoing_value = evaluate_decision_tree(tree, _features(n, outgoing_metadata))
                d_u = outgoing.u_cost - incoming.u_cost
                d_cycles = outgoing.cycle_excess - incoming.cycle_excess
                d_edges = (incoming.previous_u_mask & mask).bit_count() + (
                    mask & (mask >> 1)
                ).bit_count()
                d_rank = d_edges - d_cycles
                slack = Fraction(3 * d_u - 2 * d_rank - 1) - outgoing_value + incoming_value
                if slack < 0:
                    return {
                        "n": n,
                        "valid": False,
                        "row": outgoing.row_index,
                        "mask": mask,
                        "slack": [slack.numerator, slack.denominator],
                    }
                tight += slack == 0
                minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
                key = (outgoing.row_index, outgoing.previous_u_mask, outgoing.partition)
                children.setdefault(key, outgoing)
        representatives = children
        layer_counts.append(len(representatives))
    terminal_values = [
        evaluate_decision_tree(
            tree,
            _features(
                n,
                {
                    "row_index": state.row_index,
                    "previous_u_mask": state.previous_u_mask,
                    "partition": state.partition,
                },
            ),
        )
        for state in representatives.values()
    ]
    minimum_terminal = min(terminal_values)
    return {
        "n": n,
        "valid": minimum_terminal >= DESIRED_TERMINALS[n % 3],
        "reachable_states_by_row": layer_counts,
        "attempted": attempted,
        "accepted": accepted,
        "tight": tight,
        "minimum_slack": [minimum_slack.numerator, minimum_slack.denominator],
        "minimum_terminal_potential": [
            minimum_terminal.numerator,
            minimum_terminal.denominator,
        ],
    }


def _lp_expression(coefficients: dict[str, int], indexes: dict[str, int]) -> str:
    pieces = []
    for name, value in sorted(coefficients.items(), key=lambda item: indexes[item[0]]):
        if value == 0:
            continue
        index = indexes[name]
        pieces.append(f"{value:+d} p{index} {-value:+d} n{index}")
    return " ".join(pieces) if pieces else "0"


def write_lp(path: Path, names: list[str], constraints: list[tuple[dict[str, int], str, int]]) -> None:
    indexes = {name: index for index, name in enumerate(names)}
    objective = " ".join(f"+1 p{i} +1 n{i}" for i in range(len(names)))
    lines = ["Minimize", f" obj: {objective}", "Subject To"]
    for index, (coefficients, relation, rhs) in enumerate(constraints):
        lines.append(f" c{index}: {_lp_expression(coefficients, indexes)} {relation} {rhs}")
    lines.append("End")
    path.write_text("\n".join(lines) + "\n")


def _read_solution(path: Path, names: list[str], denominator_limit: int) -> dict[str, Fraction]:
    values: dict[str, float] = {}
    in_columns = False
    for line in path.read_text().splitlines():
        if line.startswith("# Columns"):
            in_columns = True
            continue
        if line.startswith("# Rows"):
            break
        if not in_columns or not line or line.startswith("#"):
            continue
        variable, value = line.split()
        values[variable] = float(value)
    coefficients = {}
    for index, name in enumerate(names):
        value = values.get(f"p{index}", 0.0) - values.get(f"n{index}", 0.0)
        rational = Fraction(value).limit_denominator(denominator_limit)
        if rational:
            coefficients[name] = rational
    return coefficients


def verify_constraints(
    coefficients: dict[str, Fraction], constraints: list[tuple[dict[str, int], str, int]]
) -> dict[str, int]:
    tight = 0
    for index, (terms, relation, rhs) in enumerate(constraints):
        left = sum(coefficients.get(name, Fraction(0)) * value for name, value in terms.items())
        valid = left <= rhs if relation == "<=" else left >= rhs if relation == ">=" else left == rhs
        if not valid:
            raise ValueError(f"rationalized candidate fails constraint {index}: {left} {relation} {rhs}")
        tight += left == rhs
    return {"constraints": len(constraints), "tight": tight}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--highs", type=Path, default=DEFAULT_HIGHS)
    parser.add_argument("--work-directory", type=Path, default=DEFAULT_WORK)
    parser.add_argument("--denominator-limit", type=int, default=24)
    parser.add_argument(
        "--basis", choices=("linear", "hinges", "quadratic", "lookup"), default="hinges"
    )
    parser.add_argument("--feature-level", choices=("runs", "out"), default="runs")
    parser.add_argument("--analyze-table", action="store_true")
    parser.add_argument("--validate-tree", type=int, choices=range(7, 9))
    parser.add_argument("--include-coefficients", action="store_true")
    args = parser.parse_args()
    global ACTIVE_BASIS, ACTIVE_FEATURE_LEVEL
    ACTIVE_BASIS = args.basis
    ACTIVE_FEATURE_LEVEL = args.feature_level
    if args.analyze_table:
        table = build_shortest_potential_table((3, 4, 5, 6))
        samples = [(_tree_coordinates(feature), value) for feature, value in table]
        tree = build_decision_tree(samples)
        leaves, depth = _tree_stats(tree)
        result = {
            "states": len(samples),
            "values": sorted({int(value) for _, value in samples}),
            "leaves": leaves,
            "depth": depth,
        }
        if args.validate_tree is not None:
            result["held_out"] = validate_tree_width(tree, args.validate_tree)
        print(json.dumps(result, indent=2))
        return
    names, constraints = build_constraints((3, 4, 5, 6))
    work_directory = args.work_directory.resolve()
    model = work_directory / "grid-graphs-sparse-potential.lp"
    solution = work_directory / "grid-graphs-sparse-potential.sol"
    highs = args.highs.resolve()
    work_directory.mkdir(parents=True, exist_ok=True)
    write_lp(model, names, constraints)
    solution.unlink(missing_ok=True)
    completed = subprocess.run(
        [str(highs), "--solver", "simplex", "--solution_file", str(solution), str(model)],
        check=True,
        capture_output=True,
        cwd=work_directory,
        text=True,
    )
    if "Model status        : Infeasible" in completed.stdout:
        print(
            json.dumps(
                {
                    "training_widths": [3, 4, 5, 6],
                    "basis": args.basis,
                    "feature_level": args.feature_level,
                    "basis_terms": len(names),
                    "status": "solver-reported-infeasible",
                    "solver": "HiGHS",
                },
                indent=2,
            )
        )
        return
    if "Model status        : Optimal" not in completed.stdout or not solution.exists():
        raise RuntimeError(f"HiGHS did not return an optimal solution:\n{completed.stdout}")
    coefficients = _read_solution(solution, names, args.denominator_limit)
    verification = verify_constraints(coefficients, constraints)
    result = {
        "training_widths": [3, 4, 5, 6],
        "basis": args.basis,
        "feature_level": args.feature_level,
        "basis_terms": len(names),
        "nonzero_terms": len(coefficients),
        "verification": verification,
    }
    if args.include_coefficients:
        result["coefficients"] = {
            name: [value.numerator, value.denominator]
            for name, value in sorted(coefficients.items())
        }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
