#!/usr/bin/env python3
"""Exact finite checks for the triangle and strip calculations in Ice and mirrors.

Run ``python verify_fg_strips.py`` (default ranks 2 through 8).
Only the Python standard library is required. Matrix entries are Python integers.
Positive B[u,v] denotes an arrow u -> v. Boundary vertices are omitted;
interface vertices are retained in every row and source/sink test.
These finite checks do not replace the induction in the paper.
"""

import argparse
from collections import Counter


class Quiver:
    def __init__(self):
        self.rows = {}

    def vertex(self, v):
        if v is not None:
            self.rows.setdefault(v, {})

    def add(self, u, v, amount=1):
        if u is None or v is None or u == v:
            return
        self.vertex(u)
        self.vertex(v)
        value = self.rows[u].get(v, 0) + amount
        if value:
            self.rows[u][v] = value
            self.rows[v][u] = -value
        else:
            self.rows[u].pop(v, None)
            self.rows[v].pop(u, None)

    def copy(self):
        other = Quiver()
        other.rows = {u: dict(row) for u, row in self.rows.items()}
        return other

    def delete(self, v):
        assert v in self.rows, ("missing deletion target", v)
        for u in self.rows[v]:
            del self.rows[u][v]
        del self.rows[v]

    def mutate(self, k):
        assert k in self.rows, ("missing mutation vertex", k)
        incoming = [(u, -b) for u, b in self.rows[k].items() if b < 0]
        outgoing = [(v, b) for v, b in self.rows[k].items() if b > 0]
        for u, a in incoming:
            for v, b in outgoing:
                self.add(u, v, a * b)
        for u, b in list(self.rows[k].items()):
            self.rows[k][u] = -b
            self.rows[u][k] = b

    def is_source_or_sink(self, v):
        entries = self.rows[v].values()
        return all(b >= 0 for b in entries) or all(b <= 0 for b in entries)

    def check_row(self, v, terms, context):
        expected = Counter()
        for coefficient, w in terms:
            if w in self.rows:
                expected[w] += coefficient
        expected = {w: b for w, b in expected.items() if b}
        assert self.rows[v] == expected, (context, v, self.rows[v], expected)

    def certificate(self, target, word):
        assert target in self.rows
        assert target not in word
        assert len(word) == len(set(word))
        original = self.copy()
        original.delete(target)
        for v in word:
            self.mutate(v)
        assert self.is_source_or_sink(target), ("not a source or sink", target, self.rows[target], word)
        self.delete(target)
        for v in reversed(word):
            self.mutate(v)
        assert self.rows == original.rows, ("deletion and undo changed retained entries", target)
        return 1, 2 * len(word)


def add_triangle(quiver, n, label):
    """Add exactly the oriented cycles of equation (small-triangle)."""
    for a in range(n + 1):
        for b in range(n + 1 - a):
            c = n - a - b
            if max(a, b, c) < n:
                quiver.vertex(label(a, b, c))
    for a in range(n - 1):
        for b in range(n - 1 - a):
            c = n - 2 - a - b
            u = label(a + 1, b + 1, c)
            v = label(a, b + 1, c + 1)
            w = label(a + 1, b, c + 1)
            quiver.add(u, v)
            quiver.add(v, w)
            quiver.add(w, u)


def x_label(n, a, b, c):
    return None if c == 0 else (b + c, c)


def y_label(n, a, b, c):
    return None if a == 0 else (b, b + c)


def band(n):
    result = Quiver()
    add_triangle(result, n, lambda a, b, c: x_label(n, a, b, c))
    add_triangle(result, n, lambda a, b, c: y_label(n, a, b, c))
    return result


def diagonal(k):
    return k, k


def sweep(t, start=1):
    return ([diagonal(k) for k in range(start, t)]
            + [(i, j) for i in range(start + 1, t + 1)
               for j in range(i - 1, 0, -1)])


def check_initial_rows(n):
    original = band(n)
    rotated = {(n - i, n - j): {(n - u, n - v): b for (u, v), b in row.items()}
               for (i, j), row in original.rows.items()}
    assert rotated == original.rows, ("half-turn", n)
    for t in range(2, n):
        q = original.copy()
        s = diagonal(t)
        for k in range(1, t):
            q.mutate(diagonal(k))
        q.check_row(s, [(1, (t, t - 1)), (1, (t, t + 1)),
                        (-1, (t + 1, t)), (-1, (t - 1, t))], "target-initial")
        for i in range(3, t + 1):
            for j in range(1, i - 1):
                q.check_row((i, j), [(1, (i + 1, j + 1)), (-1, (i + 1, j)),
                                      (-1, (i, j + 1)), (1, (i, j - 1)),
                                      (1, (i - 1, j)), (-1, (i - 1, j - 1))],
                            "lower-initial")
        for i in range(2, t + 1):
            for j in range(i - 1, 0, -1):
                if j == i - 1:
                    terms = [(-1, diagonal(i - 1)), (-1, (i + 1, i - 1)), (1, (i, i - 2))]
                    if i < t:
                        terms += [(1, diagonal(i))]
                    else:
                        terms += [(-1, s), (1, (t + 1, t)), (1, (t - 1, t))]
                else:
                    terms = [(-1, (i - 1, j)), (-1, (i + 1, j)),
                             (1, (i, j + 1)), (1, (i, j - 1))]
                    if i == t:
                        terms += [(-1, s)]
                q.check_row((i, j), terms, "sweep pre-pivot")
                q.mutate((i, j))
        q.check_row(s, [(-1, (t, 1)), (1, (t, t + 1))], "sweep-row")
    if n == 2:
        assert original.is_source_or_sink(diagonal(1))
    else:
        q = original.copy()
        q.certificate(diagonal(n - 1), sweep(n - 1))
        word = [(n - i, n - j) for i, j in sweep(n - 1)]
        q.certificate(diagonal(1), [v for v in word if v in q.rows])
        # Verify the stated omitted-D_1 calculation before rotating it back.
        for t in range(2, n):
            q = original.copy()
            q.delete(diagonal(1))
            ordinary = original.copy()
            ordinary.mutate(diagonal(1))
            for pivot in sweep(t)[1:]:
                if pivot[0] != pivot[1] and pivot != (2, 1):
                    expected = {v: b for v, b in ordinary.rows[pivot].items() if v in q.rows}
                    assert q.rows[pivot] == expected, ("opposite endpoint later pivot", n, t, pivot)
                q.mutate(pivot)
                ordinary.mutate(pivot)
            terms = [(-1, (t, 1)), (1, (t, t + 1))]
            if t == 2:
                terms += [(-1, (1, 2))]
            q.check_row(diagonal(t), terms, "opposite endpoint final row")


def in_cone(a, b, c, depth):
    return a > 0 and b > 0 and c > 0 and min(a + c, b + c) <= depth


def trimmed_triangle(n, p):
    q = Quiver()
    add_triangle(q, n, lambda a, b, c: None if c == 0 else (a, b, c))
    for a, b, c in list(q.rows):
        if ((a == 0 or b == 0) and (c <= p or c >= n - p)) or in_cone(a, b, c, p):
            q.delete((a, b, c))
    return q


def check_shell_rows(n, p):
    q = trimmed_triangle(n, p)
    b0 = n - p - 1
    for swapped in (False, True):
        def label(a, b, c):
            return (b, a, c) if swapped else (a, b, c)
        sign = -1 if swapped else 1
        for a in range(p, 0, -1):
            c = p + 1 - a
            target = label(a, b0, c)
            if target not in q.rows:
                continue
            word = [label(a, b, n - a - b) for b in range(1, b0)]
            r = q.copy()
            terms = [(sign, label(a - 1, b0, c + 1)),
                     (sign, label(a + 1, b0 - 1, c)),
                     (-sign, label(a, b0 - 1, c + 1))]
            r.check_row(target, terms, "triangle-target")
            for b, pivot in enumerate(word, 1):
                A = label(a - 1, b + 1, n - a - b)
                C = label(a + 1, b, n - a - b - 1)
                if b == 1:
                    incoming = {v for v, value in r.rows[pivot].items() if value * sign < 0}
                    assert incoming == {v for v in (A, C) if v in r.rows}, ("first triangle pivot", n, p, a, swapped)
                else:
                    r.check_row(pivot, [(sign, word[b - 2]), (sign, label(a, b + 1, n - a - b - 1)),
                                        (-sign, A), (-sign, C)], "triangle-pivot")
                r.mutate(pivot)
            r.check_row(target, [(sign, word[-1])] if word else [], "triangle-final")
            q.certificate(target, word)
    assert all(not in_cone(a, b, c, p + 1) for a, b, c in q.rows), ("shell incomplete", n, p)


def pruned_band(n, p):
    q = band(n)
    for i, j in list(q.rows):
        edge = i in (0, n) or i == j
        if edge:
            remove = j <= p or j >= n - p
        elif i > j:
            remove = in_cone(n - i, i - j, j, p + 1)
        else:
            remove = in_cone(i, j - i, n - j, p + 1)
        if remove:
            q.delete((i, j))
    return q


def check_pruned_rows(n, p):
    original = pruned_band(n, p)
    if n <= 2 * p + 2:
        for k in range(p + 1, n - p):
            assert original.is_source_or_sink(diagonal(k)), ("middle edge", n, p)
        return
    first = p + 2
    t = n - p - 1
    s = diagonal(t)
    for epsilon in (0, 1):
        q = original.copy()
        if epsilon:
            q.delete(diagonal(first - 1))
        word = [v for v in sweep(t, p + 1) if v in q.rows]
        H = (diagonal(first - 1) if epsilon == 0 else
             ((first - 1, first) if first < t else None))
        for pivot in word:
            i, j = pivot
            if i == j:
                q.mutate(pivot)
                continue
            if j == i - 1:
                if i < t:
                    terms = [(-1, H if i == first else diagonal(i - 1)),
                             (1, diagonal(i)), (-1, (i + 1, i - 1)), (1, (i, i - 2))]
                else:
                    terms = [(-1, s), (-1, (t + 1, t - 1)),
                             (1, (t + 1, t)), (1, (t, t - 2))]
                    if not (epsilon and first == t):
                        terms += [(-1, diagonal(t - 1)), (1, (t - 1, t))]
            else:
                terms = [(-1, H if i == first else (i - 1, j)), (-1, (i + 1, j)),
                         (1, (i, j + 1)), (1, (i, j - 1))]
                if i == t:
                    terms += [(-1, s)]
            q.check_row(pivot, terms, "pruned pre-pivot")
            q.mutate(pivot)
        terms = [(-1, (t, 1))]
        if epsilon and first == t:
            terms += [(-1, (t - 1, t))]
        q.check_row(s, terms, "pruned-final")
        assert q.is_source_or_sink(s)


def weighted_label(vertices, weights):
    return tuple(sorted((v, w) for v, w in zip(vertices, weights) if w))


def strip(n):
    """An oriented rectangle with the true boundary sides at top and bottom."""
    half = n // 2
    triangles = []
    for s in range(half):
        triangles.extend([(("T", s + 1), ("T", s), ("B", s)),
                          (("B", s), ("B", s + 1), ("T", s + 1))])
    q = Quiver()
    for vertices in triangles:
        add_triangle(q, n, lambda a, b, c, vertices=vertices:
                     None if c == 0 else weighted_label(vertices, (a, b, c)))
    return q, triangles


def band_embedding(triangles, j, n):
    """Identify the pair adjacent to edge e_j with the stated x,y band."""
    left, right = triangles[j - 1], triangles[j]
    common = set(left) & set(right)
    assert len(common) == 2
    # Each triangle is stored with true boundary c=0. The common vertex
    # on that true boundary is x_a (respectively y_b).
    xa = next(v for v in left[:2] if v in common)
    xb = next(v for v in left[:2] if v not in common)
    xc = left[2]
    ya = right[2]
    yb = next(v for v in right[:2] if v in common)
    yc = next(v for v in right[:2] if v not in common)
    assert {xa, xc} == {ya, yb}
    assert xa == ya and xc == yb

    def label(i, k):
        if i >= k:
            return weighted_label((xa, xb, xc), (n - i, i - k, k))
        return weighted_label((ya, yb, yc), (n - k, i, k - i))
    return label


def verify_strip(n):
    q, triangles = strip(n)
    N = len(triangles)
    counts = [0, 0]
    end_edges = ({("T", 0), ("B", 0)}, {("T", n // 2), ("B", n // 2)})
    protected = {v for v in q.rows if any({u for u, weight in v} <= edge for edge in end_edges)}

    def delete(target, word):
        assert target not in protected
        assert not (set(word) & protected)
        assert all(v in q.rows for v in word), ("deleted pivot in global word", target)
        result = q.certificate(target, word)
        counts[0] += result[0]
        counts[1] += result[1]

    def trim_edge(j, p):
        label = band_embedding(triangles, j, n)
        t = n - p - 1
        if t <= p:
            return
        word = sweep(t, p + 1) if t > p + 1 else []
        delete(label(t, t), [label(i, k) for i, k in word])
        other = p + 1
        if other != t:
            rotated = [label(n - i, n - k) for i, k in word]
            assert {v for v in rotated if v not in q.rows} <= {label(t, t)}
            delete(label(other, other), [v for v in rotated if v in q.rows])

    def check_stage(p):
        for j in range(p, N - p + 1):
            label = band_embedding(triangles, j, n)
            for k in range(1, n):
                if k <= p or k >= n - p:
                    assert label(k, k) not in q.rows, ("edge stage invariant", n, p, j, k)
        for index in range(p - 1, N - p + 1):
            vertices = triangles[index]
            for a in range(1, n):
                for b in range(1, n - a):
                    c = n - a - b
                    if in_cone(a, b, c, p):
                        assert weighted_label(vertices, (a, b, c)) not in q.rows, ("cone stage invariant", n, p, index)
        assert protected <= q.rows.keys()

    for j in range(1, N):
        trim_edge(j, 0)
    check_stage(1)
    for p in range(1, n // 2):
        b0 = n - p - 1
        for index in range(p, N - p):
            vertices = triangles[index]
            for swapped in (False, True):
                def label(a, b, c):
                    weights = (b, a, c) if swapped else (a, b, c)
                    return weighted_label(vertices, weights)
                for a in range(p, 0, -1):
                    target = label(a, b0, p + 1 - a)
                    if target in q.rows:
                        delete(target, [label(a, b, n - a - b) for b in range(1, b0)])
        for j in range(p + 1, N - p):
            trim_edge(j, p)
        check_stage(p + 1)
    label = band_embedding(triangles, N // 2, n)
    assert all(label(k, k) not in q.rows for k in range(1, n)), ("central edge remains", n)
    return N, *counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=8)
    args = parser.parse_args()
    assert args.max_n >= 2
    print("n triangles deletions mutations_including_undo")
    for n in range(2, args.max_n + 1):
        check_initial_rows(n)
        for p in range(1, (n - 1) // 2 + 1):
            check_shell_rows(n, p)
            check_pruned_rows(n, p)
        print(n, *verify_strip(n), flush=True)
    print("All complete-row identities, source/sink tests, and deletion/undo equalities passed.")


if __name__ == "__main__":
    main()
