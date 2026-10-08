# Network coding conjecture counterexample [ALL CONTENT IS AI GENERATED]

> **Note:** The construction comes from the XOR swap network at the core of OpenAI's sub-$n\log n$ integer multiplication algorithm, [Integer multiplication below n log n](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf) (entry 109 in [openai/math](https://github.com/openai/math)). Afshani, Freksen, Kamma and Larsen showed that the network coding conjecture implies an $\Omega(n\log n)$ lower bound for constant-degree Boolean circuits for multiplication ([arXiv:1902.10935](https://arxiv.org/abs/1902.10935)). The counterexamples were extracted using Astra 6.1 and Opus 5.5.

**Writeup:** [*Swap, Don't Route*](writeup/swap-dont-route.pdf) ([LaTeX source](writeup/swap-dont-route.tex)) — the 33-vertex counterexample (NC = 1 > 149/150 ≥ MCF), with the 32-vertex version (MCF ≤ 125/126) in Appendix C.

Counterexamples to the network coding conjecture for undirected graphs: instances where network coding achieves rate 1 but the maximum concurrent flow (routing) is strictly below 1.

| | 33-vertex (main text) | 32-vertex (Appendix C, current best) |
|---|---:|---:|
| vertices | 33 | 32 |
| edges | 91 | 84 |
| unit messages | 30 | 30 |
| source–sink pairs | 7 | 13 |
| bound | MCF ≤ 149/150 | MCF ≤ 125/126 |

## Files

- [`scripts/verify-network-coding-32.py`](scripts/verify-network-coding-32.py) — standard-library exact checker for the 32-vertex code and routing bound.
- [`scripts/cut-slack-32.py`](scripts/cut-slack-32.py) — standard-library cut-slack analysis of the 32-vertex graph, and the 31-vertex merged graph on which coding and routing tie.
- [`scripts/verify-network-coding-33.py`](scripts/verify-network-coding-33.py) — standard-library exact checker for the 33-vertex code and routing bound.
- [`writeup/`](writeup) — the LaTeX writeup, its PDF, and `gen_full_graph.py`, which draws the full-network figure from the checker's edge table.
- [`lean/`](lean) — a Lean 4 + Mathlib formalization of the 33-vertex counterexample, with no `sorry`. Its final theorem, `NetCoding.not_undirectedMultipleUnicastConjecture` in [`Main.lean`](lean/NetworkCoding33/Main.lean), refutes the conjecture with the entropy-based coding rate of Braverman–Garg–Schvartzman (Definition A.3). Along the way it proves that the XOR code achieves rate 1, that routing is at most 149/150 (by weak LP duality with distance potentials), and that the coding rate is exactly 1 (by the cut bound). All finite facts about the instance are checked by the kernel with `decide +kernel`; no `native_decide` is used.

## Running

```bash
python3 scripts/verify-network-coding-32.py
python3 scripts/cut-slack-32.py --merged
python3 scripts/verify-network-coding-33.py
```

To check the Lean proof (Lean toolchain `v4.33.1`, installed automatically by [elan](https://github.com/leanprover/elan)):

```bash
cd lean && lake exe cache get && lake build
```

## Implications

The network coding conjecture (Li and Li, 2004) says that in undirected graphs, network coding achieves no higher rate than multicommodity flow. Several superlinear lower bounds were proved *conditionally* on it, by turning a fast algorithm or small circuit into a network code and then bounding the network's flow. A counterexample means these arguments no longer give lower bounds, so this route to them is closed.

A fixed constant gap is enough. Braverman, Garg and Schvartzman ([arXiv:1608.06545](https://arxiv.org/abs/1608.06545)) show that any $(1+\varepsilon)$ gap between coding and routing can be amplified to a $(\log|G|)^c$ gap, for some constant $c<1$, so weakened versions that allow coding a constant-factor advantage fail as well.

Conditional lower bounds that relied on the conjecture:

- **Oblivious matrix transposition:** $\Omega(p\log p)$ I/Os in the I/O model, which also implies lower bounds in the oblivious cell-probe model and for two-tape oblivious Turing machines (Adler, Harvey, Jain, Kleinberg, Lehman).
- **Integer sorting and matrix transpose:** tight lower bounds for external-memory integer sorting and matrix transpose without obliviousness assumptions, and $\Omega(n\log n)$ for oblivious internal-memory sorting of $\Theta(\log n)$-bit keys (Farhadi, Hajiaghayi, Larsen, Shi).
- **Multiplication:** $\Omega(n\log n)$ size for constant-degree Boolean circuits multiplying two $n$-bit integers, via the same bound for the shift problem. The conjecture also implies one of Valiant's circuit-complexity conjectures (Afshani, Freksen, Kamma, Larsen).
- **Sorting circuits:** optimality, up to $\mathrm{poly}\log^* n$ factors, of $o(n\log n)$-size circuits for sorting $n$ keys of $k=O(\log n)$ bits (Asharov, Lin, Shi).
- **Data structures:** links to non-adaptive function inversion and polynomial evaluation and interpolation, which in turn imply superlinear circuit lower bounds for explicit functions such as integer sorting and multipoint polynomial evaluation (Dvořák, Koucký, Král, Slívová).

## A refuted theorem on layered networks

Both counterexamples also refute Theorem 6.3 of T. Xiahou, Z. Li, C. Wu, J. Huang, [A geometric perspective to multiple-unicast network coding](https://i.cs.hku.hk/~cwu/papers/txiahou-tit14.pdf), *IEEE Transactions on Information Theory* 60(5):2884–2895, 2014.

That theorem is about the cost version of the conjecture, which is equivalent to the original by LP duality: each edge has a cost instead of a capacity, and the claim is that no code meets the sessions' rates more cheaply than routing along shortest paths. Theorem 6.3 states that in a *layered* network (every edge joins two consecutive layers) in which each source and its sink lie in different layers, coding is cheaper than routing by at most the factor $\rho$ by which edge costs vary within a layer. With unit costs $\rho=1$, so coding should never be cheaper.

Both counterexamples are layered networks of this kind. With unit costs their codes cost 149 and 125, one per transmission, while routing along shortest paths costs at least 150 and 126.

The error is in Step 2 of the proof. It places each layer on a vertical line in the plane with the $\ell_\infty$ norm and asserts that the distance between each source and its sink is at most $\rho$ times the number of layers between them. That needs a monotone shortest path, one that climbs one layer per edge. In the counterexamples no path from $s_{ab}$ to $t_{ab}$ is monotone, so these two vertices are 5 edges apart but only 3 layers apart. With that extra hypothesis the theorem is true, by summing the cut bound over the cuts between consecutive layers. The writeup's section "Comparison with known results" gives the details, together with a table comparing both networks with the classes of networks on which the conjecture has been proved.

## Related resources

- M. Braverman, S. Garg, A. Schvartzman, [Network coding in undirected graphs is either very helpful or not helpful at all](https://arxiv.org/abs/1608.06545) (arXiv:1608.06545).
- R. J. Lipton and K. W. Regan, [Network Coding Yields Lower Bounds](https://rjlipton.com/2019/04/30/network-coding-yields-lower-bounds/), *Gödel's Lost Letter and P=NP*, April 30, 2019.
- R. J. Lipton and K. W. Regan, [The Network Coding Conjecture Is Powerful](https://rjlipton.com/2019/05/06/the-network-coding-conjecture-is-powerful/), *Gödel's Lost Letter and P=NP*, May 6, 2019.
- M. Adler, N. J. A. Harvey, K. Jain, R. Kleinberg, A. R. Lehman, [On the capacity of information networks](https://www.cs.ubc.ca/~nickhar/papers/Capacity/Capacity-Soda.pdf), SODA 2006.
- A. Farhadi, M. Hajiaghayi, K. G. Larsen, E. Shi, [Lower bounds for external memory integer sorting via network coding](https://arxiv.org/abs/1811.01313) (arXiv:1811.01313), STOC 2019.
- P. Afshani, C. B. Freksen, L. Kamma, K. G. Larsen, [Lower bounds for multiplication via network coding](https://arxiv.org/abs/1902.10935) (arXiv:1902.10935), ICALP 2019.
- G. Asharov, W.-K. Lin, E. Shi, [Sorting short keys in circuits of size o(n log n)](https://arxiv.org/abs/2010.09884) (arXiv:2010.09884), SODA 2021.
- P. Dvořák, M. Koucký, K. Král, V. Slívová, [Data structures lower bounds and popular conjectures](https://arxiv.org/abs/2102.09294) (arXiv:2102.09294).
