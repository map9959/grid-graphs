import unittest

from analysis.bounds.coupled_forced_forest_row_grammar import (
    coupled_transition,
    first_coupled_row_state,
    prefix_component_charge,
    reachable_coupled_layers,
    reachable_coupled_transitions,
    validate_coupled_state,
)
from analysis.bounds.forced_forest_row_grammar import first_row_state, transition


class CoupledForcedForestRowGrammarTest(unittest.TestCase):
    def test_projection_agrees_with_existing_h_grammar(self) -> None:
        for width in range(2, 6):
            for first in range(1 << width):
                coupled = first_coupled_row_state(width, first)
                ordinary = first_row_state(width, first)
                self.assertEqual(coupled is None, ordinary is None)
                if coupled is None:
                    continue
                validate_coupled_state(width, coupled)
                for second in range(1 << width):
                    result = coupled_transition(width, coupled, second)
                    projected = transition(width, ordinary, second)
                    self.assertEqual(result is None, projected is None)
                    if result is not None:
                        validate_coupled_state(width, result.state)
                        self.assertEqual(result.state.h_partition, projected.partition)

    def test_retirement_and_merger_examples(self) -> None:
        state = first_coupled_row_state(4, 0b0001)
        self.assertIsNotNone(state)
        result = coupled_transition(4, state, 0)
        self.assertIsNotNone(result)
        self.assertEqual(result.retired_f, 1)
        self.assertEqual(result.state.retired_f, 1)
        self.assertEqual(result.merged_f, 0)

    def test_f_components_never_merge_on_valid_transitions(self) -> None:
        for width in range(2, 6):
            layers = reachable_coupled_layers(width)
            for layer in layers[:-1]:
                for _state, _mask, result in reachable_coupled_transitions(width, layer):
                    self.assertEqual(result.merged_f, 0)

    def test_f_partition_is_determined_by_h_frontier_state(self) -> None:
        for width in range(2, 7):
            for layer in reachable_coupled_layers(width):
                observed = {}
                for state in layer:
                    key = (state.forced_mask, state.h_partition)
                    previous = observed.setdefault(key, state.f_partition)
                    self.assertEqual(previous, state.f_partition)

    def test_prefix_component_ledger(self) -> None:
        for width in range(2, 7):
            layers = reachable_coupled_layers(width)
            for state in layers[0]:
                expected = width + 3 - 3 * state.forced_mask.bit_count()
                self.assertEqual(prefix_component_charge(1, state), expected)
            accumulated = {
                state: width + 3 - 3 * state.forced_mask.bit_count()
                for state in layers[0]
            }
            for row, layer in enumerate(layers[:-1], start=1):
                outgoing_costs = {}
                for state, mask, result in reachable_coupled_transitions(width, layer):
                    cost = accumulated[state] + width + 3 - 3 * mask.bit_count()
                    previous = outgoing_costs.setdefault(result.state, cost)
                    self.assertEqual(previous, cost)
                    self.assertEqual(prefix_component_charge(row + 1, result.state), cost)
                accumulated = outgoing_costs


if __name__ == "__main__":
    unittest.main()
