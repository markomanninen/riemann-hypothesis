#!/usr/bin/env python3
"""Lay the modules out as a map and write the data for the mountain view.

Usage: python3 -I verification/explorer/build_mountain.py

Run build_data.py first. This script reads its module order from data/names.json and the
import graph from ../import-graph, and writes into data/:

  mountain.json     the areas (one per source folder) with their circles, the longest import
                    chain and the table of sections in the binary file
  mountain.gz.txt   the sections (positions, heights, lines, areas, import lists), gzipped and
                    then written as base64 text, because the page host serves text files only
  names.gz.txt      names.json, packed the same way

The map is a circle packing of the folder tree. A module is a circle whose area is its line
count, a folder is the circle around its modules and subfolders. The height of a module is the
length of the longest chain of imports below it.
"""
import base64
import collections
import gzip
import json
import math
import os
import statistics
import struct
import sys
from array import array

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
GRAPH = os.path.join(REPO, "verification", "import-graph")
DATA = os.path.join(HERE, "data")


def place(px, py, pr, qx, qy, qr, cr):
    """Centre of a circle of radius cr that touches circles p and q."""
    dx, dy = px - qx, py - qy
    d2 = dx * dx + dy * dy
    if not d2:
        return qx + cr, qy
    a2 = (qr + cr) ** 2
    b2 = (pr + cr) ** 2
    if a2 > b2:
        u = (d2 + b2 - a2) / (2 * d2)
        v = math.sqrt(max(0.0, b2 / d2 - u * u))
        return px - u * dx - v * dy, py - u * dy + v * dx
    u = (d2 + a2 - b2) / (2 * d2)
    v = math.sqrt(max(0.0, a2 / d2 - u * u))
    return qx + u * dx - v * dy, qy + u * dy + v * dx


def pack_siblings(r):
    """Pack circles of radii r, largest first, around the origin (the front-chain method
    of Wang et al., as in d3-hierarchy). Returns x, y and the radius of a circle around all."""
    n = len(r)
    x, y = [0.0] * n, [0.0] * n
    if n == 1:
        return x, y, r[0]
    x[0], x[1] = -r[1], r[0]
    if n == 2:
        return x, y, r[0] + r[1]
    x[2], y[2] = place(x[1], y[1], r[1], x[0], y[0], r[0], r[2])
    nxt, prv = [0] * n, [0] * n
    a, b, c = 0, 1, 2
    nxt[a], prv[c] = b, b
    nxt[b], prv[a] = c, c
    nxt[c], prv[b] = a, a
    i = 3
    while i < n:
        ri = r[i]
        cx, cy = place(x[a], y[a], r[a], x[b], y[b], r[b], ri)
        j, k, sj, sk = nxt[b], prv[a], r[b], r[a]
        hit = False
        while True:
            if sj <= sk:
                dr = r[j] + ri - 1e-6
                ddx, ddy = cx - x[j], cy - y[j]
                if dr > 0 and dr * dr > ddx * ddx + ddy * ddy:
                    b = j
                    nxt[a], prv[b] = b, a
                    hit = True
                    break
                sj += r[j]
                j = nxt[j]
            else:
                dr = r[k] + ri - 1e-6
                ddx, ddy = cx - x[k], cy - y[k]
                if dr > 0 and dr * dr > ddx * ddx + ddy * ddy:
                    a = k
                    nxt[a], prv[b] = b, a
                    hit = True
                    break
                sk += r[k]
                k = prv[k]
            if j == nxt[k]:
                break
        if hit:
            continue
        x[i], y[i] = cx, cy
        prv[i], nxt[i] = a, b
        nxt[a] = prv[b] = i
        b = i
        # The pair on the front chain that is closest to the origin takes the next circle.
        def score(m):
            m2 = nxt[m]
            ab = r[m] + r[m2]
            sx = (x[m] * r[m2] + x[m2] * r[m]) / ab
            sy = (y[m] * r[m2] + y[m2] * r[m]) / ab
            return sx * sx + sy * sy
        best, m = score(a), nxt[b]
        while m != b:
            sc = score(m)
            if sc < best:
                best, a = sc, m
            m = nxt[m]
        b = nxt[a]
        i += 1
    # A circle around all of them: move the centre towards the farthest circle, in shrinking steps.
    cx = cy = 0.0
    for step in range(1, 80):
        far, fi = -1.0, 0
        for t in range(n):
            d = math.hypot(x[t] - cx, y[t] - cy) + r[t]
            if d > far:
                far, fi = d, t
        d = math.hypot(x[fi] - cx, y[fi] - cy)
        if d > 0:
            px = x[fi] + (x[fi] - cx) / d * r[fi]
            py = y[fi] + (y[fi] - cy) / d * r[fi]
            cx += (px - cx) / (step + 1)
            cy += (py - cy) / (step + 1)
    big = max(math.hypot(x[t] - cx, y[t] - cy) + r[t] for t in range(n))
    return [v - cx for v in x], [v - cy for v in y], big


def main():
    with open(os.path.join(DATA, "names.json"), encoding="utf-8") as f:
        coded = json.load(f)
    names, prev = [], ""
    for k, rest in coded:
        prev = prev[:k] + rest
        names.append(prev)
    n = len(names)
    ident = {m: i for i, m in enumerate(names)}

    lines, height = [0] * n, [0] * n
    with gzip.open(os.path.join(GRAPH, "modules.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for row in f:
            p = row.rstrip("\n").split("\t")
            if p[0] in ident:
                lines[ident[p[0]]], height[ident[p[0]]] = int(p[1]), int(p[4])
    imports = [[] for _ in range(n)]
    with gzip.open(os.path.join(GRAPH, "edges.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for row in f:
            a, b = row.rstrip("\n").split("\t")
            if b in ident:
                imports[ident[a]].append(ident[b])

    # The folder tree.
    subdirs, leaves, seen = collections.defaultdict(list), collections.defaultdict(list), {""}
    for i, m in enumerate(names):
        d = m.rpartition(".")[0]
        leaves[d].append(i)
        while d not in seen:
            seen.add(d)
            parent = d.rpartition(".")[0]
            subdirs[parent].append(d)
            d = parent

    packed = {}

    def pack(d):
        items = [("d", c, pack(c)) for c in subdirs[d]]
        items += [("m", i, math.sqrt(max(lines[i], 4))) for i in leaves[d]]
        items.sort(key=lambda t: (-t[2], str(t[1])))
        gap = 0.5 if not subdirs[d] else 1.5 + 0.02 * max(t[2] for t in items)
        x, y, big = pack_siblings([t[2] + gap for t in items])
        packed[d] = (items, x, y)
        sys.stderr.write(f"\rpacked {len(packed)} of {len(seen)} folders")
        return big

    radius = pack("")
    sys.stderr.write("\n")

    # Absolute positions, and the areas in depth-first order so that an area's subareas are
    # the index range [index, index + span).
    mx, my = [0.0] * n, [0.0] * n
    area_of = [0] * n
    areas = []

    def walk(d, ox, oy, here):
        items, x, y = packed[d]
        stats = [0, 0, []]
        for (kind, key, r), dx, dy in zip(items, x, y):
            if kind == "m":
                mx[key], my[key], area_of[key] = ox + dx, oy + dy, here
                stats[0] += 1
                stats[1] += lines[key]
                stats[2].append(height[key])
        for (kind, key, r), dx, dy in zip(items, x, y):
            if kind == "d":
                idx = len(areas)
                areas.append({"name": key, "parent": here, "x": ox + dx, "y": oy + dy, "r": r})
                sub = walk(key, ox + dx, oy + dy, idx)
                a = areas[idx]
                a["span"] = len(areas) - idx
                a["modules"], a["lines"] = sub[0], sub[1]
                a["h"] = [min(sub[2]), int(statistics.median(sub[2])), max(sub[2])]
                stats[0] += sub[0]
                stats[1] += sub[1]
                stats[2].extend(sub[2])
        return stats

    walk("", 0.0, 0.0, -1)

    # The longest chain of imports, from the top module down.
    top = max(height)
    chain = [0]
    while height[chain[-1]]:
        here = chain[-1]
        chain.append(next(b for b in imports[here] if height[b] == height[here] - 1))

    q = lambda v: max(0, min(65535, round((v / radius * 0.5 + 0.5) * 65535)))
    xy = array("H", [0]) * (2 * n)
    for i in range(n):
        xy[2 * i], xy[2 * i + 1] = q(mx[i]), q(my[i])
    off, tgt = array("I", [0]) * (n + 1), array("I")
    for i in range(n):
        tgt.extend(sorted(imports[i]))
        off[i + 1] = len(tgt)
    sections = [("off", "u32", off), ("tgt", "u32", tgt), ("xy", "u16", xy),
                ("lines", "u16", array("H", [min(v, 65535) for v in lines])),
                ("area", "u16", array("H", area_of)), ("height", "u8", array("B", height))]
    blob, table = b"", []
    for name, kind, data in sections:
        if sys.byteorder != "little":
            data.byteswap()
        raw = data.tobytes()
        table.append({"name": name, "type": kind, "offset": len(blob), "length": len(data)})
        blob += raw + b"\0" * (-len(raw) % 4)
    with open(os.path.join(DATA, "mountain.gz.txt"), "wb") as f:
        f.write(base64.b64encode(gzip.compress(blob, 9, mtime=0)))
    with open(os.path.join(DATA, "names.json"), "rb") as src, open(os.path.join(DATA, "names.gz.txt"), "wb") as f:
        f.write(base64.b64encode(gzip.compress(src.read(), 9, mtime=0)))

    rnd = lambda v: round(v / radius, 5)
    meta = {
        "modules": n, "lines": sum(lines), "edges": len(tgt), "top": top, "radius": round(radius, 2),
        "chain": chain, "sections": table,
        # [name, parent, x, y, r, span, modules, lines, lowest, median and highest height]
        "areas": [[a["name"], a["parent"], rnd(a["x"]), rnd(a["y"]), rnd(a["r"]), a["span"],
                   a["modules"], a["lines"], *a["h"]] for a in areas],
    }
    with open(os.path.join(DATA, "mountain.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f, separators=(",", ":"))
    print(f"modules {n}, areas {len(areas)}, radius {radius:.0f}, chain {len(chain)} modules")
    for name in ("mountain.json", "mountain.gz.txt", "names.gz.txt"):
        print(f"{name}: {os.path.getsize(os.path.join(DATA, name)):,} bytes")


if __name__ == "__main__":
    main()
