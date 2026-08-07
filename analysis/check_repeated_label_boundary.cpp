#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

struct Dsu {
  std::array<int, 25> parent{};

  explicit Dsu(int size) {
    for (int i = 0; i < size; ++i) parent[i] = i;
  }

  int find(int value) {
    while (parent[value] != value) {
      parent[value] = parent[parent[value]];
      value = parent[value];
    }
    return value;
  }

  bool join(int left, int right) {
    left = find(left);
    right = find(right);
    if (left == right) return false;
    parent[right] = left;
    return true;
  }
};

struct Census {
  std::uint64_t valid = 0;
  std::uint64_t maximal = 0;
  int minimum_rl_slack = std::numeric_limits<int>::max();
  bool noncrossing_failure = false;
  std::uint32_t owner_hall_failure = 0;
  std::uint32_t witness_matching_failure = 0;
  std::uint32_t center_repeat_failure = 0;
  std::uint32_t interior_witness_failure = 0;
};

bool is_u(std::uint32_t mask, int vertex) { return (mask >> vertex) & 1U; }

std::vector<int> neighbors(int n, int vertex) {
  std::vector<int> result;
  int row = vertex / n;
  int column = vertex % n;
  if (row > 0) result.push_back(vertex - n);
  if (row + 1 < n) result.push_back(vertex + n);
  if (column > 0) result.push_back(vertex - 1);
  if (column + 1 < n) result.push_back(vertex + 1);
  return result;
}

std::vector<std::pair<int, int>> grid_edges(int n) {
  std::vector<std::pair<int, int>> result;
  for (int row = 0; row < n; ++row) {
    for (int column = 0; column < n; ++column) {
      int vertex = row * n + column;
      if (row + 1 < n) result.push_back({vertex, vertex + n});
      if (column + 1 < n) result.push_back({vertex, vertex + 1});
    }
  }
  return result;
}

std::vector<int> boundary_order(int n) {
  std::vector<int> result;
  for (int column = 0; column < n; ++column) result.push_back(column);
  for (int row = 1; row < n; ++row) result.push_back(row * n + n - 1);
  for (int column = n - 2; column >= 0; --column)
    result.push_back((n - 1) * n + column);
  for (int row = n - 2; row > 0; --row) result.push_back(row * n);
  return result;
}

int count_roots(Dsu &dsu, const std::vector<int> &vertices) {
  std::array<bool, 25> roots{};
  for (int vertex : vertices) roots[dsu.find(vertex)] = true;
  return std::count(roots.begin(), roots.end(), true);
}

bool boundary_labels_noncrossing(Dsu &h, const std::vector<int> &boundary) {
  std::array<bool, 25> present{};
  for (int vertex : boundary) present[h.find(vertex)] = true;
  for (int first = 0; first < 25; ++first) {
    if (!present[first]) continue;
    for (int second = first + 1; second < 25; ++second) {
      if (!present[second]) continue;
      std::vector<int> word;
      for (int vertex : boundary) {
        int label = h.find(vertex);
        if (label == first || label == second) word.push_back(label);
      }
      if (word.empty()) continue;
      int changes = 0;
      for (std::size_t i = 0; i < word.size(); ++i)
        changes += word[i] != word[(i + 1) % word.size()];
      if (changes >= 4) return false;
    }
  }
  return true;
}

bool augment(int u, const std::array<std::uint32_t, 25> &choices,
             std::array<int, 25> &matched, std::uint32_t &seen) {
  std::uint32_t remaining = choices[u] & ~seen;
  while (remaining) {
    int label = __builtin_ctz(remaining);
    remaining &= remaining - 1;
    seen |= 1U << label;
    if (matched[label] == -1 || augment(matched[label], choices, matched, seen)) {
      matched[label] = u;
      return true;
    }
  }
  return false;
}

void analyze(int n, std::uint32_t mask,
             const std::vector<std::pair<int, int>> &edges, Census &census) {
  int vertex_count = n * n;
  Dsu h(vertex_count);
  for (auto [left, right] : edges) {
    if (is_u(mask, left) && is_u(mask, right)) continue;
    if (!h.join(left, right)) return;
  }
  ++census.valid;

  auto boundary = boundary_order(n);
  if (!boundary_labels_noncrossing(h, boundary)) census.noncrossing_failure = true;

  std::array<std::uint32_t, 25> witness_choices{};
  bool maximal = true;
  bool every_repeat_uses_center = true;
  bool every_witness_touches_boundary = true;
  std::array<bool, 25> h_touches_boundary{};
  for (int vertex : boundary) h_touches_boundary[h.find(vertex)] = true;

  for (int u = 0; u < vertex_count; ++u) {
    if (!is_u(mask, u)) continue;
    std::array<int, 25> multiplicity{};
    ++multiplicity[h.find(u)];
    for (int v : neighbors(n, u))
      if (is_u(mask, v)) ++multiplicity[h.find(v)];
    bool center_repeated = multiplicity[h.find(u)] >= 2;
    bool has_repeat = false;
    for (int label = 0; label < vertex_count; ++label) {
      if (multiplicity[label] >= 2) {
        has_repeat = true;
        witness_choices[u] |= 1U << label;
        if (!h_touches_boundary[label]) every_witness_touches_boundary = false;
      }
    }
    maximal &= has_repeat;
    every_repeat_uses_center &= center_repeated;
  }
  if (!maximal) return;
  ++census.maximal;

  Dsu f(vertex_count);
  std::vector<int> f_vertices;
  std::vector<int> all_vertices;
  for (int vertex = 0; vertex < vertex_count; ++vertex) {
    all_vertices.push_back(vertex);
    if (!is_u(mask, vertex)) f_vertices.push_back(vertex);
  }
  for (auto [left, right] : edges)
    if (!is_u(mask, left) && !is_u(mask, right)) f.join(left, right);

  int boundary_f = 0;
  std::array<int, 25> boundary_weight_by_f{};
  for (int vertex : boundary) {
    if (is_u(mask, vertex)) continue;
    int row = vertex / n;
    int column = vertex % n;
    int weight = 1 + ((row == 0 || row == n - 1) &&
                      (column == 0 || column == n - 1));
    boundary_f += weight;
    boundary_weight_by_f[f.find(vertex)] += weight;
  }
  int c_f = count_roots(f, f_vertices);
  int c_h = count_roots(h, all_vertices);
  census.minimum_rl_slack = std::min(
      census.minimum_rl_slack, 3 * n - 4 + c_f + c_h - boundary_f);

  // For owner-only Hall charging, optimize |X|-|F-owners|-|H-owners|.
  // Components with the same H owner form independent groups.
  std::array<int, 25> owner_group_profit{};
  for (int root = 0; root < vertex_count; ++root) {
    if (!boundary_weight_by_f[root]) continue;
    owner_group_profit[h.find(root)] += boundary_weight_by_f[root] - 1;
  }
  int maximum_owner_excess = 0;
  for (int label = 0; label < vertex_count; ++label)
    maximum_owner_excess += std::max(0, owner_group_profit[label] - 1);
  if (maximum_owner_excess > 3 * n - 4 && !census.owner_hall_failure)
    census.owner_hall_failure = mask;

  std::array<int, 25> matched;
  matched.fill(-1);
  bool matching_exists = true;
  for (int u = 0; u < vertex_count; ++u) {
    if (!is_u(mask, u)) continue;
    std::uint32_t seen = 0;
    if (!augment(u, witness_choices, matched, seen)) {
      matching_exists = false;
      break;
    }
  }
  if (!matching_exists && !census.witness_matching_failure)
    census.witness_matching_failure = mask;
  if (!every_repeat_uses_center && !census.center_repeat_failure)
    census.center_repeat_failure = mask;
  if (!every_witness_touches_boundary && !census.interior_witness_failure)
    census.interior_witness_failure = mask;
}

std::string pattern(int n, std::uint32_t mask) {
  std::string result;
  for (int row = 0; row < n; ++row) {
    if (row) result += '/';
    for (int column = 0; column < n; ++column)
      result += is_u(mask, row * n + column) ? 'U' : '.';
  }
  return result;
}

int main() {
  for (int n = 2; n <= 5; ++n) {
    auto edges = grid_edges(n);
    Census total;
    std::uint64_t limit = std::uint64_t{1} << (n * n);

#pragma omp parallel
    {
      Census local;
#pragma omp for schedule(static)
      for (std::uint64_t mask = 0; mask < limit; ++mask)
        analyze(n, static_cast<std::uint32_t>(mask), edges, local);
#pragma omp critical
      {
        total.valid += local.valid;
        total.maximal += local.maximal;
        total.minimum_rl_slack =
            std::min(total.minimum_rl_slack, local.minimum_rl_slack);
        total.noncrossing_failure |= local.noncrossing_failure;
        if (!total.owner_hall_failure)
          total.owner_hall_failure = local.owner_hall_failure;
        if (!total.witness_matching_failure)
          total.witness_matching_failure = local.witness_matching_failure;
        if (!total.center_repeat_failure)
          total.center_repeat_failure = local.center_repeat_failure;
        if (!total.interior_witness_failure)
          total.interior_witness_failure = local.interior_witness_failure;
      }
    }

    std::cout << "n=" << n << " valid=" << total.valid
              << " maximal=" << total.maximal
              << " min_RL_slack=" << total.minimum_rl_slack
              << " noncrossing_failure=" << total.noncrossing_failure << '\n';
    auto print_witness = [&](const char *name, std::uint32_t mask) {
      std::cout << "  " << name << '=';
      if (mask)
        std::cout << pattern(n, mask) << " (mask " << mask << ')';
      else
        std::cout << "none";
      std::cout << '\n';
    };
    print_witness("owner_Hall_failure", total.owner_hall_failure);
    print_witness("witness_matching_failure", total.witness_matching_failure);
    print_witness("center_repeat_failure", total.center_repeat_failure);
    print_witness("interior_witness_failure", total.interior_witness_failure);

    const std::array<std::uint64_t, 4> expected_valid = {9, 100, 2278, 116252};
    if (total.valid != expected_valid[n - 2] || total.noncrossing_failure ||
        total.minimum_rl_slack < 0)
      return 1;
  }
}
