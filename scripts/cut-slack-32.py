#!/usr/bin/env python3
"""Obstructions to shrinking the 32-vertex construction (standard library only).

    python3 scripts/cut-slack-32.py            # cut slack of every edge of the 32-vertex graph
    python3 scripts/cut-slack-32.py --merged   # the 31-vertex graph G = t_22 with its 124-slot code

Part 1.  In the undirected model every code satisfies the cut bound
    capacity(delta S) >= number of unit messages with exactly one endpoint in S
for every vertex set S.  Over a large family of sets S (all sets of at most four
vertices, every union of layer-and-type classes, and those unions with one vertex
added or removed) the script reports, for each edge, the smallest slack found.  An
edge with slack 0 cannot lose capacity in any code at all, so only the edges listed
with positive slack could carry fewer transmissions in a cheaper code.

Part 2.  Merging the hub G with the sink t_22 gives a 31-vertex graph on which the
hop sum drops to 124.  Because the merged vertex already knows w_22, the code can be
shortened by one transmission (q_22 sends x_22 clean, G computes y_22 itself, the
reply from Z is dropped).  The script re-verifies that 124-transmission code and
reports hop sum 124 = capacity 124: coding and routing tie, so this is one
transmission short of a 31-vertex counterexample.
"""
import importlib.util
import itertools
import sys
from pathlib import Path
from collections import defaultdict, deque

spec = importlib.util.spec_from_file_location("v32", Path(__file__).resolve().parent / "verify-network-coding-32.py")
v32 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v32)


def traffic_of(T):
    cap = defaultdict(int)
    for p, q, _ in T:
        cap[frozenset((p, q))] += 1
    return cap


def hop_sum(cap, msgs):
    adj = defaultdict(set)
    for e in cap:
        p, q = tuple(e)
        adj[p].add(q)
        adj[q].add(p)
    total, cache = 0, {}
    for src, dst in msgs.values():
        if src not in cache:
            cache[src] = v32.bfs(adj, src)
        total += cache[src][dst]
    return total


def min_slack(cap, msgs):
    verts = sorted({u for e in cap for u in e})
    adj = defaultdict(dict)
    for e, c in cap.items():
        p, q = tuple(e)
        adj[p][q] = c
        adj[q][p] = c
    demand = defaultdict(int)
    for src, dst in msgs.values():
        demand[(src, dst)] += 1
    best = {e: None for e in cap}

    def consider(S):
        c = sum(adj[p][q] for p in S for q in adj[p] if q not in S)
        d = sum(n for (src, dst), n in demand.items() if (src in S) != (dst in S))
        assert c >= d, ("cut bound violated", sorted(S))
        for p in S:
            for q in adj[p]:
                if q not in S:
                    e = frozenset((p, q))
                    if best[e] is None or c - d < best[e]:
                        best[e] = c - d

    family = [set(c) for k in range(1, 5) for c in itertools.combinations(verts, k)]
    classes = defaultdict(set)
    for u in verts:
        classes[(v32.LAYER[u[0]], u[0])].add(u)
    keys = sorted(classes)
    unions = [set().union(*(classes[k] for k in comb))
              for r in range(1, len(keys)) for comb in itertools.combinations(keys, r)]
    for S in unions:
        family.append(S)
        for u in verts:
            family.append(S | {u})
            family.append(S - {u})
    for S in family:
        if 0 < len(S) < len(verts):
            consider(S)
    return best


def merged_protocol():
    """Merge G and t_22, then shorten the code by one transmission."""
    cap, msgs, T = v32.build()
    f = lambda u: "G" if u == "t22" else u
    msgs = {m: (f(s), f(d)) for m, (s, d) in msgs.items()}
    y22 = ["z22", "alpha22.12", "alpha22.32"]
    out = []
    for p, q, bits in T:
        p, q = f(p), f(q)
        par = {b for b in set(bits) if bits.count(b) % 2}
        if (p, q) == ("q22", "G") and "x22" in par and "beta22" in par:
            bits = ["x22"]                      # F_22 -> x_22: G already knows w_22
        elif (p, q) == ("G", "Z") and par == {"beta22"} | set(y22):
            bits = y22                          # beta_22 + y_22 -> y_22
        elif (p, q) == ("Z", "G") and par == set(y22):
            continue                            # the reply y_22 is no longer needed
        out.append((p, q, bits))
    return cap, msgs, out


def report(cap, msgs, T, title):
    verts = {u for e in cap for u in e}
    print(f"{title}: {len(verts)} vertices, {len(cap)} edges, capacity {sum(cap.values())}, "
          f"{len(msgs)} unit messages, hop sum {hop_sum(cap, msgs)}")
    best = min_slack(cap, msgs)
    free = sorted((tuple(sorted(e, key=lambda u: (v32.LAYER[u[0]], u))), cap[e], s)
                  for e, s in best.items() if s >= 1)
    print(f"  edges on a tight cut (cannot lose capacity in any code): {sum(1 for s in best.values() if s == 0)}")
    print(f"  edges with positive cut slack: {len(free)}")
    for (p, q), c, s in free:
        print(f"    {p}-{q}  capacity {c}  slack {s}")


if __name__ == "__main__":
    if "--merged" in sys.argv:
        cap0, msgs, T = merged_protocol()
        cap = traffic_of(T)
        n = v32.check_protocol(cap, msgs, T)
        print(f"merged code verified: {n} transmissions, every sink decodes")
        report(cap, msgs, T, "31-vertex graph G = t22")
    else:
        cap, msgs, T = v32.build()
        v32.check_protocol(cap, msgs, T)
        report(cap, msgs, T, "32-vertex graph")
