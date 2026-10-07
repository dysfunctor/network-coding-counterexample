#!/usr/bin/env python3
"""Exact checker for the 32-vertex XOR construction (standard library only).

The 3 x 2 table, with the source hub O deleted:
32 vertices, 84 edges, total capacity 125, and 30 unit messages whose
breadth-first-search distances sum to 126.

    python3 scripts/verify-network-coding-32.py
    python3 scripts/verify-network-coding-32.py --print-edges

Cells i = (a, b) with rows a = 1..3 and columns b = 1, 2.  ibar is the other
cell of row a, and Col(i) the two other cells of column b.

Raw bits (all independent):
    x_i       at s_i,  demanded at t_i
    z_i       at H,    demanded at Z
    beta_i    at H,    demanded at Z
    alpha_ij  at s_j,  demanded at Z     (j in Col(i))
Derived forms: y_i = z_i + sum_j alpha_ij,  w_i = x_i + y_i.

Checks, with no numerical optimisation:
  1. Each raw bit is a basis vector over F_2.  Before each transmission,
     elimination confirms that the sender can compute the transmitted form;
     afterwards every sink must compute its demanded bit.
  2. Two-direction traffic on every edge equals an independently written
     capacity table; no other edge is used.
  3. Every edge joins consecutive layers 0..4.
  4. No layer-increasing path leads from s_i to t_i (exhaustive search).
  5. Hop distances of all demands by breadth-first search, and the totals.
"""
import argparse
from collections import defaultdict, deque
from fractions import Fraction

LAYER = {"H": 0, "s": 0, "C": 1, "p": 1, "D": 2, "q": 2, "G": 3, "t": 3, "Z": 4}
ROWS, COLS = (1, 2, 3), (1, 2)
CELLS = [(a, b) for a in ROWS for b in COLS]


def bar(i):
    return (i[0], 3 - i[1])


def col(i):
    return [j for j in CELLS if j[1] == i[1] and j != i]


def v(kind, i):
    return f"{kind}{i[0]}{i[1]}"


def build():
    x = lambda i: v("x", i)
    z = lambda i: v("z", i)
    be = lambda i: v("beta", i)
    al = lambda i, j: f"alpha{i[0]}{i[1]}.{j[0]}{j[1]}"
    y = lambda i: [z(i)] + [al(i, j) for j in col(i)]          # derived form
    w = lambda i: [x(i)] + y(i)                                  # derived form
    P = lambda b: [x(i) for i in CELLS if i[1] == b]
    Q = lambda a: w((a, 1)) + w((a, 2))

    # ---- explicit capacity table (written independently of the protocol) ---
    cap = {}

    def edge(p, q, c):
        k = frozenset((p, q))
        assert len(k) == 2 and k not in cap, (p, q)
        cap[k] = c

    for i in CELLS:
        a, b = i
        edge(v("s", i), f"C{b}", 1)
        edge(f"C{b}", v("q", i), 1)
        edge("H", v("p", i), 2)
        edge(v("p", i), f"D{a}", 1)
        edge(f"D{a}", v("t", i), 1)
        edge(v("q", i), "G", 3)
        edge(v("t", i), "Z", 2)
        edge(v("p", bar(i)), v("q", i), 1)
        edge(v("q", i), v("t", bar(i)), 1)
        for j in col(i):
            edge(v("s", j), v("p", i), 1)
            edge(v("p", i), v("q", j), 1)
    for b in COLS:
        edge(f"C{b}", "H", 1)
    for a in ROWS:
        edge(f"D{a}", "G", 1)
    edge("G", "Z", 18)

    # ---- raw bits: name -> (source, sink) -------------------------------------
    msgs = {}
    for i in CELLS:
        msgs[x(i)] = (v("s", i), v("t", i))
        msgs[z(i)] = ("H", "Z")
        msgs[be(i)] = ("H", "Z")
        for j in col(i):
            msgs[al(i, j)] = (v("s", j), "Z")

    # ---- the protocol, in causal order (one row per line of the note's table) -
    T = []
    send = lambda p, q, bits: T.append((p, q, list(bits)))
    for i in CELLS:
        send(v("s", i), f"C{i[1]}", [x(i)])
        send(f"C{i[1]}", v("q", i), [x(i)])
    for b in COLS:
        send(f"C{b}", "H", P(b))
    for i in CELLS:
        send("H", v("p", i), [z(i)] + P(i[1]))
    for i in CELLS:
        for j in col(i):
            send(v("s", j), v("p", i), [al(i, j), x(j)])
            send(v("p", i), v("q", j), [al(i, j), x(j)])
            send(v("q", j), "G", [al(i, j)])
            send("G", "Z", [al(i, j)])
    for i in CELLS:
        send("H", v("p", bar(i)), [be(i)])
    for i in CELLS:
        send(v("p", i), f"D{i[0]}", w(i))
        send(f"D{i[0]}", v("t", i), w(i))
    for i in CELLS:
        vi = [be(i)] + w(bar(i))
        send(v("p", bar(i)), v("q", i), vi)
        send(v("q", i), v("t", bar(i)), vi)
        send(v("t", bar(i)), "Z", [be(i)])
    for a in ROWS:
        send(f"D{a}", "G", Q(a))
    for i in CELLS:
        F = [x(i), be(i)] + w(bar(i))
        send(v("q", i), "G", F)
        send("G", "Z", F + Q(i[0]))
    for i in CELLS:
        send("Z", v("t", i), y(i))
    return cap, msgs, T


def check_protocol(cap, msgs, T):
    index = {m: k for k, m in enumerate(sorted(msgs))}
    know = defaultdict(dict)

    def reduce(basis, vec):
        while vec:
            top = vec.bit_length() - 1
            if top not in basis:
                return vec
            vec ^= basis[top]
        return 0

    def learn(node, vec):
        vec = reduce(know[node], vec)
        if vec:
            know[node][vec.bit_length() - 1] = vec

    for m, (src, _) in msgs.items():
        learn(src, 1 << index[m])
    traffic = defaultdict(int)
    for p, q, bits in T:
        vec = 0
        for m in bits:
            vec ^= 1 << index[m]
        assert reduce(know[p], vec) == 0, f"{p} cannot compute {bits}"
        k = frozenset((p, q))
        assert k in cap, f"transmission on a non-edge {p}-{q}"
        traffic[k] += 1
        learn(q, vec)
    for k, c in cap.items():
        assert traffic[k] == c, f"edge {sorted(k)}: traffic {traffic[k]} != capacity {c}"
    for m, (_, dst) in msgs.items():
        assert reduce(know[dst], 1 << index[m]) == 0, f"{dst} cannot decode {m}"
    return len(T)


def bfs(adj, src, ok=lambda p, q: True):
    dist, todo = {src: 0}, deque([src])
    while todo:
        p = todo.popleft()
        for q in adj[p]:
            if q not in dist and ok(p, q):
                dist[q] = dist[p] + 1
                todo.append(q)
    return dist


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--print-edges", action="store_true")
    args = ap.parse_args()

    cap, msgs, T = build()
    vertices = {u for k in cap for u in k}
    layer = {u: LAYER[u[0]] for u in vertices}
    n_sends = check_protocol(cap, msgs, T)
    assert all(abs(layer[p] - layer[q]) == 1 for p, q in map(tuple, cap))

    adj = defaultdict(list)
    for k in cap:
        p, q = tuple(k)
        adj[p].append(q)
        adj[q].append(p)
    up = lambda p, q: layer[q] == layer[p] + 1
    for i in CELLS:
        assert v("t", i) not in bfs(adj, v("s", i), up), f"layer-increasing path for x{i}"

    demand = defaultdict(int)
    for src, dst in msgs.values():
        demand[(src, dst)] += 1
    need, hist, cache = 0, defaultdict(int), {}
    for (src, dst), d in demand.items():
        if src not in cache:
            cache[src] = bfs(adj, src)
        h = cache[src][dst]
        need += d * h
        hist[h] += d
    total = sum(cap.values())

    print(f"vertices {len(vertices)}, edges {len(cap)}, transmissions {n_sends}")
    print(f"unit messages {len(msgs)} in {len(demand)} source-sink pairs; "
          f"messages by hop distance {dict(sorted(hist.items()))}")
    print("protocol: every sender knows each transmitted form, every edge carries exactly "
          "its capacity, every sink decodes  -> NC >= 1")
    print("every edge joins consecutive layers; no layer-increasing s_i -> t_i path")
    print(f"total capacity {total}, required capacity at rate 1: {need}")
    assert need > total
    print(f"=> MCF <= {Fraction(total, need)} < 1 <= NC")
    if args.print_edges:
        for k in sorted(cap, key=lambda k: sorted(k)):
            p, q = sorted(k, key=lambda u: (layer[u], u))
            print(f"  {p}-{q}  capacity {cap[k]}")


if __name__ == "__main__":
    main()
