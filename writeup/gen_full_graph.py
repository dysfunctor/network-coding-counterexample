"""Generate the TikZ for the full-network figure in swap-dont-route.tex from the checker's edge table.

Layers run from left to right. Column 1 of the grid is drawn above the hubs and column 2 below,
each with rows 1 to 3 from top to bottom, so the vertices of a cell lie on one horizontal line.

Usage: python3 writeup/gen_full_graph.py > full-graph.tex
"""
import importlib.util
from pathlib import Path
import sys
from collections import Counter

REPO = str(Path(__file__).resolve().parent.parent)
spec = importlib.util.spec_from_file_location("verify33", f"{REPO}/scripts/verify-network-coding-33.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

cap, msgs, T = mod.build(3, 2, True)
assert len(cap) == 91 and sum(cap.values()) == 149

DX = 2.9                      # horizontal distance between layers (cm)
ROW = 0.95                    # vertical distance between the rows of a column (cm)
INNER = 2.14                  # distance from the hub axis to the nearest row of a column, in rows
HUBS = ("O", "H", "G", "Z")


def layer(v):
    return mod.LAYER[v[0]]


def shared(v):
    return v in HUBS or v[0] in "CD"


def pos(v):
    if v in HUBS:
        y = 0.0
    elif v[0] == "C":
        y = {"1": 0.5, "2": -0.5}[v[1]] * ROW
    elif v[0] == "D":
        y = {"1": 1.0, "2": 0.0, "3": -1.0}[v[1]] * ROW
    else:
        a, b = int(v[1]), int(v[2])
        y = (INNER + 3 - a) * ROW if b == 1 else -(INNER + a - 1) * ROW
    return layer(v) * DX, y


def kind(u, v):
    names = {u, v}
    if names in ({"O", "H"}, {"G", "Z"}):
        return "trunk"
    cellv = [n for n in names if n[0] in "spqt"]
    if len(cellv) == 2:
        (k1, a1, b1), (k2, a2, b2) = [(n[0], n[1], n[2]) for n in sorted(cellv, key=layer)]
        if b1 == b2 and a1 != a2 and (k1, k2) in (("s", "p"), ("p", "q")):
            return "col"
        if a1 == a2 and b1 != b2 and (k1, k2) in (("p", "q"), ("q", "t")):
            return "row"
        raise ValueError((u, v))
    return "gray"


def tex_name(v):
    if v in HUBS:
        return f"${v}$"
    if v[0] in "CD":
        # the checker calls the row parity vertices D_a; the writeup calls them R_a
        return f"${'R' if v[0] == 'D' else v[0]}_{{{v[1]}}}$"
    return f"${v[0]}_{{{v[1:]}}}$"


edges = []
for k, c in cap.items():
    u, v = sorted(k, key=lambda n: (layer(n), n))
    edges.append((u, v, c, kind(u, v)))

counts = Counter(e[3] for e in edges)
assert counts == {"gray": 53, "col": 24, "row": 12, "trunk": 2}, counts
assert all(layer(v) == layer(u) + 1 for u, v, _, _ in edges)

order = {"gray": 0, "col": 1, "row": 2, "trunk": 3}
edges.sort(key=lambda e: (order[e[3]], e[2], e[0], e[1]))
vertices = sorted({n for k in cap for n in k}, key=lambda n: (layer(n), -pos(n)[1]))
ytop = max(pos(v)[1] for v in vertices)
ybot = min(pos(v)[1] for v in vertices)

out = []
w = out.append
w("\\begin{tikzpicture}[x=1cm,y=1cm]")
for v in vertices:
    x, y = pos(v)
    w(f"\\coordinate ({v}) at ({x:.2f},{y:.2f});")
for u, v, c, kd in edges:
    style = {"gray": "fg", "col": "fcol", "row": "frow", "trunk": "ftrunk"}[kd]
    if kd != "trunk":
        style += f", cap{min(c, 3)}"
    w(f"\\draw[{style}] ({u}) -- ({v});")
for u, v in (("O", "H"), ("G", "Z")):
    w(f"\\node[font=\\scriptsize, above=1.5pt] at ($({u})!0.5!({v})$) {{{cap[frozenset((u, v))]}}};")
for v in vertices:
    w(f"\\node[{'boxsh' if shared(v) else 'box'}] at ({v}) {{{tex_name(v)}}};")
for b, y in ((1, (INNER + 1) * ROW), (2, -(INNER + 1) * ROW)):
    w(f"\\node[font=\\footnotesize, text=black!60] at (0,{y:.2f}) {{column {b}}};")
ya = ybot - 0.75
w(f"\\draw[black!45, line width=0.4pt] (0,{ya:.2f}) -- ({5*DX:.2f},{ya:.2f});")
for L in range(6):
    w(f"\\draw[black!45, line width=0.4pt] ({L*DX:.2f},{ya:.2f}) -- ++(0,0.1);")
    w(f"\\node[lay, below=1pt] at ({L*DX:.2f},{ya:.2f}) {{{L}}};")
w(f"\\node[lay] at ({2.5*DX:.2f},{ya-0.62:.2f}) {{layer}};")
w("\\end{tikzpicture}")

sys.stdout.write("\n".join(out) + "\n")
print(f"% {len(edges)} edges, capacity {sum(e[2] for e in edges)}, {dict(counts)}", file=sys.stderr)
