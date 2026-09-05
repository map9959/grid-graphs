#!/usr/bin/env python3
"""Analyze exact coupled-interval lookup values for max-plus formulas."""

from __future__ import annotations

from collections import Counter, defaultdict

from coupled_interval_potential import enumerate_source, solve


def numeric(feature: tuple) -> tuple[int, ...]:
    if feature in (("initial",), ("zero",)):
        return ()
    (phase, boundary, reserve, width, forced, runs, left, right, h_count,
     f_count, retired_h, retired_f, maxima) = feature
    observed = dict(maxima)
    return (
        width,
        forced,
        runs,
        left,
        right,
        h_count,
        f_count,
        retired_h,
        retired_f,
        *(observed.get(key, 0) for key in ((0, 0), (0, 1), (1, 0), (1, 1))),
    )


def main() -> None:
    sources = [enumerate_source(width) for width in range(3, 9)]
    result = solve(sources, "extrema", True)
    assert result["feasible"]
    values = result["potential_values"]
    by_mode = defaultdict(list)
    for feature, value in values:
        if feature in (("initial",), ("zero",)):
            continue
        by_mode[(feature[0], feature[1], feature[2])].append((numeric(feature), value))
    for mode, observations in sorted(by_mode.items(), key=repr):
        print(mode, "states", len(observations), "values", dict(sorted(Counter(v for _, v in observations).items())))
        affine_hints = Counter()
        for data, value in observations:
            (width, forced, runs, left, right, h_count, f_count, retired_h,
             retired_f, m00, m01, m10, m11) = data
            candidates = {
                "w-3f": width - 3 * forced,
                "w-3f+3r": width - 3 * forced + 3 * runs,
                "3h+3f-w": 3 * h_count + 3 * f_count - width,
                "max": max(m00, m01, m10, m11),
                "3max": 3 * max(m00, m01, m10, m11),
                "w-3f+3max": width - 3 * forced + 3 * max(m00, m01, m10, m11),
            }
            for name, candidate in candidates.items():
                affine_hints[(name, value - candidate)] += 1
        print("  best residuals", affine_hints.most_common(8))


if __name__ == "__main__":
    main()
