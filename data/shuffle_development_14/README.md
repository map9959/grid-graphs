# Boundary-shuffle development measurements

These are previously examined states, not held-out inputs. The probe is
tested on both recorded pre-gain states and their surrounding neutral paths,
plus the previous eight comparison starts. Geometric shuffles are always
checked by actual forced-forest connectivity. General two-for-three probes
provide a development comparison, with their cutoffs retained explicitly.

```bash
cargo build --release --bin shuffle_study --bin neutral_plateau
target/release/shuffle_study development data/shuffle_development_14
```

Timing calls disable diagnostic cycle reconstruction. A separate diagnostic
call records the length of one detected cycle per rejection; those lengths
are not necessarily the shortest cycles or a unique attribution of failure.
