#!/usr/bin/env python3
"""Exact checker for the layered two-hub XOR construction (standard library only).

Default: the 3 x 2 table -> 33 vertices, 91 edges, total capacity 149, and
30 unit messages that each need at least 5 hops (150 > 149).

    python3 scripts/verify-network-coding-33.py                  # 3 x 2 table
    python3 scripts/verify-network-coding-33.py --rows 2 --cols 3
    python3 scripts/verify-network-coding-33.py --split-aux      # alpha -> q, beta from p
    python3 scripts/verify-network-coding-33.py --print-edges

What is checked, with no numerical optimisation anywhere:
  1. Every raw bit is a distinct basis vector over F_2.  Before each
     transmission, Gaussian elimination confirms that the sender can already
     compute the transmitted linear form.  Afterwards every sink must be able to
     compute its demanded bit.
  2. The traffic on every undirected edge (both directions together) equals
     the capacity given by an explicit edge table built independently of the
     protocol; no other edge is used.
  3. Every edge joins consecutive layers 0..5.
  4. No layer-increasing path leads from s_ab to t_ab (searched exhaustively).
  5. Breadth-first-search hop distances of all demands, and the totals
     sum(capacity) < sum(demand * hop distance), which bounds the max
     concurrent multicommodity flow strictly below 1.
"""
import argparse
from collections import defaultdict, deque
from fractions import Fraction

LAYER = {"O": 0, "H": 1, "s": 1, "C": 2, "p": 2, "D": 3, "q": 3, "G": 4, "t": 4, "Z": 5}


def build(R, K, merged):
    rows, cols = range(1, R + 1), range(1, K + 1)
    cells = [(a, b) for a in rows for b in cols]
    N, A, B = len(cells), K * R * (R - 1), R * K * (K - 1)

    s = lambda a, b: f"s{a}{b}"
    p = lambda a, b: f"p{a}{b}"
    q = lambda a, b: f"q{a}{b}"
    t = lambda a, b: f"t{a}{b}"
    C = lambda b: f"C{b}"
    D = lambda a: f"D{a}"
    x = lambda a, b: f"x{a}{b}"
    y = lambda a, b: f"y{a}{b}"
    al = lambda i, j, b: f"alpha{i}{j}{b}"   # i != j in column b
    be = lambda a, i, j: f"beta{a}{i}{j}"    # i != j in row a
    w = lambda a, b: [x(a, b), y(a, b)]
    others = lambda rng, i: [j for j in rng if j != i]

    # ---- explicit edge table (independent of the protocol below) ----------
    cap = {}

    def edge(u, v, c):
        k = frozenset((u, v))
        assert len(k) == 2 and k not in cap, (u, v)
        cap[k] = c

    for (a, b) in cells:
        edge("O", s(a, b), R - 1)
        edge(s(a, b), C(b), 1)
        edge(C(b), q(a, b), 1)
        edge("H", p(a, b), 1 + (K - 1 if merged else 0))
        edge(p(a, b), D(a), 1)
        edge(D(a), t(a, b), 1)
        edge(q(a, b), "G", 1 + (R - 1 if merged else 0))
        edge(t(a, b), "Z", K)
    for b in cols:
        edge(C(b), "H", 1)
        for i in rows:
            for j in others(rows, i):
                edge(s(j, b), p(i, b), 1)
                edge(p(i, b), q(j, b), 1)
    for a in rows:
        edge(D(a), "G", 1)
        for i in cols:
            for j in others(cols, i):
                edge(p(a, j), q(a, i), 1)
                edge(q(a, i), t(a, j), 1)
    edge("O", "H", N + (B if merged else 0))
    edge("G", "Z", N + (A if merged else 0))

    # ---- messages: name -> (source, sink) ----------------------------------
    msgs = {}
    for (a, b) in cells:
        msgs[x(a, b)] = (s(a, b), t(a, b))
        msgs[y(a, b)] = ("O", "Z")
    for b in cols:
        for i in rows:
            for j in others(rows, i):
                msgs[al(i, j, b)] = ("O", "Z" if merged else q(j, b))
    for a in rows:
        for i in cols:
            for j in others(cols, i):
                msgs[be(a, i, j)] = ("O" if merged else p(a, j), "Z")

    # ---- the protocol, in causal order --------------------------------------
    T = []
    send = lambda u, v, bits: T.append((u, v, list(bits)))
    for b in cols:                                     # column pass
        P = [x(j, b) for j in rows]
        for i in rows:
            for j in others(rows, i):
                send("O", s(j, b), [al(i, j, b)])
        for j in rows:
            send(s(j, b), C(b), [x(j, b)])
            send(C(b), q(j, b), [x(j, b)])
        send(C(b), "H", P)                             # column parity, layer 2 -> 1
        for i in rows:
            mask = [al(i, j, b) for j in others(rows, i)]
            send("O", "H", [y(i, b)] + mask)
            send("H", p(i, b), [y(i, b)] + P + mask)   # u_ib
        for i in rows:
            for j in others(rows, i):
                send(s(j, b), p(i, b), [al(i, j, b), x(j, b)])
                send(p(i, b), q(j, b), [al(i, j, b), x(j, b)])
                if merged:                             # q_jb has decoded alpha
                    send(q(j, b), "G", [al(i, j, b)])
                    send("G", "Z", [al(i, j, b)])
    for a in rows:                                     # row pass
        if merged:
            for i in cols:
                for j in others(cols, i):
                    send("O", "H", [be(a, i, j)])
                    send("H", p(a, j), [be(a, i, j)])
        for j in cols:
            send(p(a, j), D(a), w(a, j))
            send(D(a), t(a, j), w(a, j))
        for i in cols:
            for j in others(cols, i):
                v = [be(a, i, j)] + w(a, j)
                send(p(a, j), q(a, i), v)
                send(q(a, i), t(a, j), v)
                send(t(a, j), "Z", [be(a, i, j)])
        Q = sum((w(a, j) for j in cols), [])
        send(D(a), "G", Q)                             # row parity
        for i in cols:
            F = [x(a, i)] + sum(([be(a, i, j)] + w(a, j) for j in others(cols, i)), [])
            send(q(a, i), "G", F)
            send("G", "Z", F + Q)                      # = y_ai + sum_j beta_aij
        for i in cols:
            send("Z", t(a, i), [y(a, i)])
    return cap, msgs, T


def check_protocol(cap, msgs, T):
    index = {m: k for k, m in enumerate(sorted(msgs))}
    know = defaultdict(dict)                 # vertex -> {pivot bit: vector}

    def reduce(basis, v):
        while v:
            top = v.bit_length() - 1
            if top not in basis:
                return v
            v ^= basis[top]
        return 0

    def learn(vertex, v):
        v = reduce(know[vertex], v)
        if v:
            know[vertex][v.bit_length() - 1] = v

    for m, (src, _) in msgs.items():
        learn(src, 1 << index[m])
    traffic = defaultdict(int)
    for u, v, bits in T:
        vec = 0
        for m in bits:
            vec ^= 1 << index[m]
        assert reduce(know[u], vec) == 0, f"{u} cannot compute {bits}"
        k = frozenset((u, v))
        assert k in cap, f"transmission on a non-edge {u}-{v}"
        traffic[k] += 1
        learn(v, vec)
    for k, c in cap.items():
        assert traffic[k] == c, f"edge {sorted(k)}: traffic {traffic[k]} != capacity {c}"
    for m, (_, dst) in msgs.items():
        assert reduce(know[dst], 1 << index[m]) == 0, f"{dst} cannot decode {m}"
    return len(T)


def neighbours(cap):
    adj = defaultdict(list)
    for k in cap:
        u, v = tuple(k)
        adj[u].append(v)
        adj[v].append(u)
    return adj


def bfs(adj, src, ok=lambda u, v: True):
    dist, todo = {src: 0}, deque([src])
    while todo:
        u = todo.popleft()
        for v in adj[u]:
            if v not in dist and ok(u, v):
                dist[v] = dist[u] + 1
                todo.append(v)
    return dist


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", type=int, default=3)
    ap.add_argument("--cols", type=int, default=2)
    ap.add_argument("--split-aux", action="store_true",
                    help="alpha bits end at q_jb and beta bits start at p_aj")
    ap.add_argument("--print-edges", action="store_true")
    args = ap.parse_args()
    R, K, merged = args.rows, args.cols, not args.split_aux
    assert R >= 1 and K >= 1

    cap, msgs, T = build(R, K, merged)
    vertices = {v for k in cap for v in k}
    layer = {v: LAYER[v[0]] for v in vertices}

    n_sends = check_protocol(cap, msgs, T)
    assert all(abs(layer[u] - layer[v]) == 1 for u, v in map(tuple, cap))

    adj = neighbours(cap)
    up = lambda u, v: layer[v] == layer[u] + 1
    for m, (src, dst) in msgs.items():
        if m.startswith("x"):
            assert dst not in bfs(adj, src, up), f"layer-increasing path for {m}"

    demand = defaultdict(int)
    for src, dst in msgs.values():
        demand[(src, dst)] += 1
    need, dist_hist, cache = 0, defaultdict(int), {}
    for (src, dst), d in demand.items():
        if src not in cache:
            cache[src] = bfs(adj, src)
        h = cache[src][dst]
        need += d * h
        dist_hist[h] += d
    total = sum(cap.values())

    N = R * K
    print(f"table {R} x {K}: N={N} cells, auxiliaries {'O->Z' if merged else 'split'}")
    print(f"vertices {len(vertices)}, edges {len(cap)}, transmissions {n_sends}")
    print(f"unit messages {len(msgs)} in {len(demand)} source-sink pairs; "
          f"messages by hop distance {dict(sorted(dist_hist.items()))}")
    print("protocol: every sender knows each transmitted form, every edge carries exactly "
          "its capacity, every sink decodes  -> NC >= 1")
    print("every edge joins consecutive layers; no layer-increasing s_ab -> t_ab path")
    print(f"total capacity {total}, required capacity at rate 1: {need}, "
          f"difference {need - total} (= N - R - K = {N - R - K})")
    if need > total:
        print(f"=> MCF <= {Fraction(total, need)} < 1 <= NC")
    else:
        print("=> this table gives no strict gap")
    if args.print_edges:
        for k in sorted(cap, key=lambda k: sorted(k)):
            u, v = sorted(k, key=lambda z: (layer[z], z))
            print(f"  {u}-{v}  capacity {cap[k]}")


if __name__ == "__main__":
    main()
