# Full Degree Spanning Tree Problem on Square Grid Graphs

This repository contains Lean code, as well as all accompanying documentation and Python/Rust support code to search for results. I assembled this repository to both publicly verify the formula and show the full work process in hopes that AI can be

## The problem

An undirected graph is a pair $(V,E)$, where $V$ is a set of vertices and $E$ is a set of edges. Each edge is a set of two elements of $V$.

A grid graph $G(m,n)$, where $m,n$ are integers greater than $0$, is a graph of $m \times n$ vertices that can be indexed as $(i,j)$, $0 \leq i < m$, $0 \leq j < n$, where each vertex has an edge connecting it to $(i+1,j)$ if $i < m-1$, $(i-1,j)$ if $i > 0$, $(i,j+1)$ if $j < n-1$, $(i,j-1)$ if $j > 0$. In simpler terms, a grid graph is a graph that's a grid over some finite rectangle of points.

A cycle is a sequence $v_0,v_1,\ldots,v_\ell$ with $\ell\geq 3$, where each consecutive pair is joined by an edge, $v_\ell=v_0$, and $v_0,\ldots,v_{\ell-1}$ are all distinct. A graph is acyclic if it has no cycles.

A graph is connected if any two distinct vertices can be joined by a path: a sequence of distinct vertices starting at one and ending at the other, with an edge between each consecutive pair.

A spanning tree $T \coloneqq (V_T,E_T)$ of an undirected graph $(V,E)$ is a connected, acyclic subgraph containing every vertex of the original graph. In particular, $V_T=V$ and $E_T\subseteq E$.

A "full-degree" vertex in a spanning tree is a vertex where all edges containing the vertex in the original graph exist in the spanning tree. As in, none of its edges were "cut" to form the tree.

This repository contains a closed formula, and a direct construction, for the maximum number of full degree vertices in a spanning tree of an grid graph of size $n \times n$.

This is the culmination of four years of chipping away at the problem with significant acceleration by LLMs at the end.

## The exact formula

Let $P(n,n)$ be the maximum number of full-degree vertices in a spanning tree of the $n \times n$ grid graph. For every positive integer $n$, write $n=3k+s$ with $s\in\{0,1,2\}$.

| Remainder $s$ | Range | $P(n,n)$ |
|---|---|---|
| $0$ | $k\ge 1$ | $3k^2+3k-2$ |
| $1$ | $k\ge 5$ | $3k^2+5k+\left\lfloor(3k-13)/10\right\rfloor$ |
| $2$ | $k\ge 6$ | $3k^2+7k-\left\lfloor(k-5)/7\right\rfloor-[n\equiv 35\pmod{42}]$ |

The bracket is $1$ when $n\equiv 35\pmod{42}$ and $0$ otherwise. The remaining small sides are:

| $n$ | 1 | 2 | 4 | 5 | 7 | 8 | 10 | 11 | 13 | 14 | 17 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $P(n,n)$ | 1 | 2 | 8 | 11 | 22 | 27 | 42 | 49 | 68 | 77 | 110 |

The [Lean theorem `GridGraphs.maxPreserved_square_exact`](lean/GridGraphs/Results/SquareFormula.lean) proves the formula for every positive side. See the [proof overview](docs/EXACT_SQUARE_FORMULA.md) and the [Lean build instructions](lean/README.md).

## Citations

Acquaviva, Sarah, "The Full Degree Spanning Tree Problem" (2023). Theses, Dissertations and Culminating Projects. 1292.
https://digitalcommons.montclair.edu/etd/1292 

R. Bhatia, S. Khuller, R. Pless, and Y. J. Sussmann. The full-degree spanning tree problem. Networks, 36(4):203–209, 2000.

## Acknowledgements

Thank you to Dong Kim for introducing me to this problem.

## License

This repository was nearly entirely generated with LLMs with the exception of this README. To the extent allowed by law, it is licensed under the Apache 2.0 license.