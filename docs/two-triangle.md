# Two-triangle coordinates and strip contributions

This module implements proof-blueprint Section 3 and manuscript `main.tex:3767–3792`.
The depth predicates come from blueprint Section 2 and `main.tex:3498–3509`.
Import `FgStrip.TwoTriangle` explicitly.

All names below have prefix `FgStrip.TwoTriangle`, unless otherwise indicated.

## Coordinates and omitted sides

`Square n = Fin (n+1) × Fin (n+1)` and

\[
\operatorname{Grid}(n)=\{(i,j):0\le i\le n,\ 0<j<n\}.
\]

`Grid` has constructive `Fintype` and `DecidableEq` instances. The maps are

\[
x(a,b,c)=(b+c,c),\qquad y(a,b,c)=(b,b+c).
\]

`x_injective`, `y_injective` and `x_eq_y_iff` prove exactly

\[
x(p)=y(q)\iff p_b=0,\ q_c=0,\ p_a=q_a,\ p_c=q_b.
\]

`x_retained_iff` and `y_retained_iff` omit exactly `x:c=0` and `y:a=0`.
`Grid.lower`, `Grid.upper`, `Grid.x_lower`, `Grid.y_upper` and `Grid.covered`
provide inverse barycentric coordinates on both closed halves of the grid.
The diagonal is represented in both halves with the stated endpoint weights.

The labels `L k`, `D k`, `R k` take `k : Triangle.EdgeWeight n` and have
coordinates `(0,k)`, `(k,k)`, `(n,k)`. `X i j hj hji hi` and `Y i j hi hij hj`
require precisely `0<j<i<n` and `0<i<j<n`, respectively. `label_cases`
classifies every grid vertex into these five families. `x_D`, `y_D`, `x_R`,
`y_L`, `x_X`, `y_Y` prove their barycentric descriptions.

## Complete signed entries

`matrix n : Matrix (Grid n) (Grid n) ℤ` restricts the sum
`Triangle.mapMatrix x + Triangle.mapMatrix y` after omission.
`matrix_cycle_sum` proves its equality to the two elementary cycle sums.
`matrix_entry` gives the same sum with every cell endpoint written in grid
coordinates. Neither definition assumes an adjacency or deletion assertion.

For a proposition `P`, write `[P]` for `1` if `P` and `0` otherwise.
`arrows u v` is the following six-term natural number, with
`u=(i,j)` and `v=(h,k)`:

\[
\begin{aligned}
A(u,v)={}&[j<i<n,\ h=i+1,\ k=j+1]\
 &+[j<i,\ h+1=i,\ k=j]\
 &+[j\le i<n,\ h=i,\ k+1=j]\
 &+[0<i\le j,\ h=i,\ k=j+1]\
 &+[0<i<j,\ h+1=i,\ k+1=j]\
 &+[i<j,\ h=i+1,\ k=j].
\end{aligned}
\]

`arrowCount_formula` derives this from the delivered `Triangle.arrowCount`.
The six `x_first_second_iff`, `x_second_third_iff`, `x_third_first_iff`,
`y_first_second_iff`, `y_second_third_iff`, `y_third_first_iff` prove existence
of each contributing cell. Injectivity of its first endpoint proves multiplicity
one. Thus every coefficient, including interface coefficients, is determined by

```lean
matrix_formula (u v : Grid n) :
  matrix n u v = (arrows u v : ℤ) - arrows v u
```

`matrix_zero_of_not_neighbours` proves that every entry outside the six
horizontal, vertical and equal-diagonal neighbour directions is zero.
The formulas quantify over all retained grid vertices and all ranks.
No finite-rank computation replaces them.

## Half-turn and depth predicates

`H` has coordinates `(n-i,n-j)`. `H_H` proves it is an involution.
`H_D`, `H_L`, `H_R`, `H_X`, `H_Y` give its action on every label family:

\[
D_k\mapsto D_{n-k},\quad L_k\mapsto R_{n-k},\quad
X_{i,j}\mapsto Y_{n-i,n-j}.
\]

`matrix_halfturn` states `matrix n (H u) (H v) = matrix n u v`.
It follows from `HSquare_x`, `HSquare_y`, cyclic permutation of barycentric
coordinates, and reindexing the actual elementary cells. `mapMatrix_rot`
preserves orientation; `mapMatrix_swap` negates it.

`EdgeDepth n p k` is `k ≤ p ∨ n-p ≤ k`. `deletedEdge` restricts this predicate
to `L`, `D`, `R`; `deletedEdge_L`, `deletedEdge_D`, `deletedEdge_R` give the
label tests. `edgeDepth_reverse` proves invariance under `k ↦ n-k`.

`BarycentricC p v` means positivity of all three coordinates and
`v.a+v.c ≤ p ∨ v.b+v.c ≤ p`. The coordinate conditions are

\[
\begin{aligned}
C^x_p(i,j)&\iff 0<j<i<n,\quad n-(i-j)\le p\ \text{or}\ i\le p,\\
C^y_p(i,j)&\iff 0<i<j<n,\quad n-(j-i)\le p\ \text{or}\ n-i\le p.
\end{aligned}
\]

`CX_x_iff` proves the first correspondence. `CY_y_iff` and `CY_rot` prove
that the second uses `(b,c,a)`, exactly as the source requires.
`Pair.CX_face` and `Pair.CY_face` transport them to the actual strip-face
coordinates in both parities. These results have no shell-deletion hypothesis.

## Every adjacent strip pair

`Pair N` has two constructors:

| Constructor | `faceX`, `faceY` | `tx(a,b,c)`, `ty(a,b,c)` | `sign` | Common edge |
| --- | --- | --- | --- | --- |
| `Pair.odd i` | `(i,false)`, `(i,true)` | `(a,b,c)`, `(b,c,a)` | `1` | `2*i+1` |
| `Pair.even i hi` | `(i,true)`, `(i+1,false)` | `(b,a,c)`, `(c,b,a)` | `-1` | `2*i+2` |

The hypothesis `hi` is `i+1<N`. `Pair.ofEdge j h0 hN` constructs a pair for
every transverse edge `0<j<2*N`. `Pair.commonEdge_ofEdge` proves its index is `j`.
This covers arbitrary strip length and both parities.

`Pair.gx` and `Pair.gy` apply these permutations and then `Strip.glue`.
`Pair.gx_eq_gy_iff` follows from the delivered `Strip.glue_opposite_iff`.
`Pair.gx_mixed`, `Pair.gy_mixed` verify the actual boundary omission.
The explicit map `Pair.embed` uses the lower barycentric representative for
`j≤i` and the upper representative otherwise. Its exported embedding is

```lean
Pair.embedding (s : Pair N) : Grid n ↪ Strip.Vertex n N
```

`Pair.gx_eq_embed_iff` and `Pair.gy_eq_embed_iff` compare every triangle vertex,
including omitted ones, to this map. `Pair.mem_range_embed_iff` proves that the
image consists exactly of the retained points on the two selected faces.
This establishes the gluing correspondence without assuming a matrix identity.

`Pair.embed_D_edge`, `Pair.embed_R_edge`, `Pair.embed_L_edge` identify the labels
with `Strip.edgeEmbedding` on `commonEdge`, `firstEdge`, `lastEdge`, respectively.
`Pair.edges_consecutive` proves that these indices are consecutive. Grid `R`
is the earlier strip edge and grid `L` the later edge. The strip's bottom
endpoint weight is `k` in the odd case and `n-k` in the even case, as specified
by `Pair.stripWeight`. `Pair.depth_stripWeight` preserves the depth test.

## Selected contribution and outside faces

`faceContribution f` is the delivered triangle cycle sum after `Strip.glue f`,
restricted to retained strip vertices. Define

\[
B_s=B_{s.\mathrm{faceX}}+B_{s.\mathrm{faceY}},\qquad
E_s=\sum_{f\notin\{s.\mathrm{faceX},s.\mathrm{faceY}\}}B_f.
\]

These are `Pair.contribution` and `Pair.remainder`. The main interfaces are

```lean
Pair.contribution_eq (s : Pair N) (u v : Grid n) :
  s.contribution (s.embed u) (s.embed v) = s.sign * matrix n u v

Pair.strip_decomposition (s : Pair N) :
  Strip.matrix n N = s.contribution + s.remainder

Pair.remainder_row_zero (s : Pair N) (u : Grid n)
    (hi : 0 < u.i) (hin : u.i < n) (v : Strip.Vertex n N) :
  s.remainder (s.embed u) v = 0
```

`Pair.contribution_eq` includes every `L` and `R` entry. Its proof uses cell
rotation and reversal, with no orientation hypothesis supplied by the caller.
`Pair.gx_ne_outside`, `Pair.gy_ne_outside` and `Pair.embed_ne_outside` derive
absence from every other face using the foundation's exact gluing classification.
The row theorem quantifies over all strip columns. `Pair.remainder_D`,
`Pair.remainder_X`, `Pair.remainder_Y` specialize it to the common edge and interiors.
`Pair.contribution_skew` and `Pair.remainder_skew` prove skew symmetry.

`Pair.contribution_zero_of_not_range` gives zero rows outside the pair image.
Together with `contribution_eq`, this identifies the contribution as the signed
extension by zero of the grid matrix. `Pair.strip_row_eq_contribution` applies
on `0<i<n`. There is no assertion that the entire induced strip block equals
the grid matrix: `Pair.strip_decomposition` retains the outside contribution.
