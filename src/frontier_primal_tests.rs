//! Independent primal checks of the frontier transition and rank bound.
use super::*;
use grid_graphs::certificate_corpus::{observe, Board};

#[test]
fn independent_primal_agrees_on_every_n4_subset() {
    let n = 4;
    let schedule = steps(n).unwrap();
    let mut optimum_u = n * n;
    for mask in 0usize..1 << (n * n) {
        let board = Board {
            n,
            preserved: (0..n * n).map(|v| mask & (1 << v) == 0).collect(),
        };
        let primal = observe(&board).is_ok();
        let mut state = Some(State::new(0, 0));
        for (v, step) in schedule.iter().enumerate() {
            state = state.and_then(|s| advance(s, step, mask & (1 << v) != 0));
        }
        assert_eq!(state.is_some(), primal, "U mask={mask:x}");
        if primal {
            optimum_u = optimum_u.min(mask.count_ones() as usize);
        }
    }
    for target in 0..=n * n {
        assert_eq!(search(n, target).unwrap().feasible, target >= optimum_u);
    }
}

#[test]
fn n17_witness_replay_and_rank_bound_use_all_17_columns() {
    let original = Board::parse(include_str!(
        "../analysis/residue_two_affine_17_witness.txt"
    ))
    .unwrap();
    assert_eq!(observe(&original).unwrap().features["f"], 110);
    // Fixed replays, never optimization above side 15.
    for symmetry in 0..8 {
        for thinning in 0..4 {
            let n = original.n;
            let mut b = Board {
                n,
                preserved: vec![false; n * n],
            };
            for y in 0..n {
                for x in 0..n {
                    let (mut yy, mut xx) = (y, x);
                    if symmetry >= 4 {
                        xx = n - 1 - xx;
                    }
                    for _ in 0..symmetry % 4 {
                        (yy, xx) = (xx, n - 1 - yy);
                    }
                    b.preserved[yy * n + xx] = original.preserved[y * n + x]
                        && (thinning == 0 || (y * n + x) % 7 != thinning);
                }
            }
            observe(&b).unwrap();
            let target = b.preserved.iter().filter(|&&f| !f).count();
            let dual_nodes = (n - 1) * (n - 1) + 1;
            let mut state = State::new(0, 0);
            let mut cost = 0;
            for (v, step) in steps(n).unwrap().iter().enumerate() {
                assert!(step.before.len().max(step.after_indices.len()) <= MAX_N);
                let (next, _) = extend_chunk(&[(state, cost)], step, target, dual_nodes);
                let expected = advance(state, step, !b.preserved[v])
                    .expect("valid witness lost by transition");
                cost += u16::from(!b.preserved[v]);
                assert_eq!(
                    next.get(&expected),
                    Some(&cost),
                    "symmetry={symmetry} vertex={v}"
                );
                state = expected;
            }
        }
    }
}
