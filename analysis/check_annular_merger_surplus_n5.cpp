#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
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

constexpr int N = 5;
constexpr int V = N * N;

bool is_u(std::uint32_t mask, int vertex) { return (mask >> vertex) & 1U; }

std::vector<std::pair<int, int>> grid_edges() {
  std::vector<std::pair<int, int>> result;
  for (int row = 0; row < N; ++row) {
    for (int column = 0; column < N; ++column) {
      int vertex = row * N + column;
      if (row + 1 < N) result.push_back({vertex, vertex + N});
      if (column + 1 < N) result.push_back({vertex, vertex + 1});
    }
  }
  return result;
}

std::array<int, 16> boundary_order() {
  return {0, 1, 2, 3, 4, 9, 14, 19, 24, 23, 22, 21, 20, 15, 10, 5};
}

int component_count(Dsu &dsu, const std::vector<int> &vertices) {
  std::array<bool, 25> roots{};
  for (int vertex : vertices) roots[dsu.find(vertex)] = true;
  return std::count(roots.begin(), roots.end(), true);
}

struct Result {
  bool valid = false;
  int merger_margin = 0;
  int ledger = 0;
};

Result analyze(std::uint32_t mask, const std::vector<std::pair<int, int>> &edges) {
  Dsu h(V);
  for (auto [left, right] : edges) {
    if (is_u(mask, left) && is_u(mask, right)) continue;
    if (!h.join(left, right)) return {};
  }

  Dsu f(V);
  std::vector<int> f_vertices;
  int q_u = 0;
  for (int vertex = 0; vertex < V; ++vertex) {
    int row = vertex / N;
    int column = vertex % N;
    if (is_u(mask, vertex)) {
      q_u += (row == 0 || row == N - 1) + (column == 0 || column == N - 1);
    } else {
      f_vertices.push_back(vertex);
    }
  }
  for (auto [left, right] : edges) {
    if (!is_u(mask, left) && !is_u(mask, right)) f.join(left, right);
  }
  std::vector<int> all_vertices(V);
  for (int vertex = 0; vertex < V; ++vertex) all_vertices[vertex] = vertex;
  int ledger = q_u + component_count(f, f_vertices) + component_count(h, all_vertices);

  auto boundary = boundary_order();
  Dsu hb(V), fb(V);
  for (int index = 0; index < 16; ++index) {
    int left = boundary[index];
    int right = boundary[(index + 1) % 16];
    if (!(is_u(mask, left) && is_u(mask, right))) hb.join(left, right);
    if (!is_u(mask, left) && !is_u(mask, right)) fb.join(left, right);
  }

  std::array<bool, 25> attached_h{}, attached_f{};
  int teeth_h = 0, teeth_f = 0, rho = 0;
  const std::array<std::pair<int, int>, 12> radial = {
      std::pair{1, 6}, {2, 7}, {3, 8}, {5, 6}, {10, 11}, {15, 16},
      {9, 8}, {14, 13}, {19, 18}, {21, 16}, {22, 17}, {23, 18}};
  for (auto [outer, inner] : radial) {
    if (is_u(mask, inner)) ++rho;
    if (!(is_u(mask, outer) && is_u(mask, inner))) {
      ++teeth_h;
      attached_h[hb.find(outer)] = true;
    }
    if (!is_u(mask, outer) && !is_u(mask, inner)) {
      ++teeth_f;
      attached_f[fb.find(outer)] = true;
    }
  }
  int a_h = std::count(attached_h.begin(), attached_h.end(), true);
  int a_f = std::count(attached_f.begin(), attached_f.end(), true);
  int margin = rho - (teeth_h - a_h) - (teeth_f - a_f);

  return {true, margin, ledger};
}

int main() {
  auto edges = grid_edges();
  std::uint64_t valid = 0;
  int minimum_margin = std::numeric_limits<int>::max();
  int minimum_ledger = std::numeric_limits<int>::max();
  std::uint32_t margin_witness = 0, ledger_witness = 0;

#pragma omp parallel
  {
    std::uint64_t local_valid = 0;
    int local_margin = std::numeric_limits<int>::max();
    int local_ledger = std::numeric_limits<int>::max();
    std::uint32_t local_margin_witness = 0, local_ledger_witness = 0;
#pragma omp for schedule(static)
    for (std::uint32_t mask = 0; mask < (1U << V); ++mask) {
      Result result = analyze(mask, edges);
      if (!result.valid) continue;
      ++local_valid;
      if (result.merger_margin < local_margin) {
        local_margin = result.merger_margin;
        local_margin_witness = mask;
      }
      if (result.ledger < local_ledger) {
        local_ledger = result.ledger;
        local_ledger_witness = mask;
      }
    }
#pragma omp critical
    {
      valid += local_valid;
      if (local_margin < minimum_margin) {
        minimum_margin = local_margin;
        margin_witness = local_margin_witness;
      }
      if (local_ledger < minimum_ledger) {
        minimum_ledger = local_ledger;
        ledger_witness = local_ledger_witness;
      }
    }
  }

  std::cout << "valid=" << valid << " minimum_merger_margin=" << minimum_margin
            << " margin_witness=" << margin_witness
            << " minimum_ledger=" << minimum_ledger
            << " ledger_witness=" << ledger_witness << '\n';
  if (valid != 116252 || minimum_margin != 4 || minimum_ledger != 12) return 1;
}
