# Glued FG strip construction

This implements Section 1 of `target-theorem.pdf` (source
`docs/tex/target-theorem.tex`). The manuscript source is `main.tex`,
lines 3134–3151 and 3368–3383. The corresponding blueprint is
`docs/tex/proof-blueprint.tex`, Section 1.

The delivered matrix is `FgStrip.Strip.matrix n N :
Matrix (FgStrip.Strip.Vertex n N) (FgStrip.Strip.Vertex n N) Int`.
It is the signed sum of the specified cycles, after gluing and actual boundary
omission. No mutation or deletion hypothesis enters its definition.

## Finite representation and coordinates

`FgStrip.Triangle.Vertex n` consists of triples of natural weights with
`a+b+c=n` and `a<n`, `b<n`, `c<n`. Coordinates use `Fin (n+1)`.
For a nonnegative triple of total weight `n`, the three strict inequalities
exclude exactly the three corners. `Triangle.Interior n` requires all three
weights to be positive. `Triangle.Cell n` consists of triples satisfying
`a+b+c+2=n`. Its `first`, `second`, and `third` vertices are

\[
(a+1,b+1,c),\quad(a,b+1,c+1),\quad(a+1,b,c+1).
\]

`Triangle.cycleCount x y z u v` counts arrows from `u` to `v` in
`x → y → z → x`. `cycleEntry` subtracts the reverse count.
`Triangle.mapMatrix_eq_sum` identifies the signed multiplicity matrix with
its elementary cycle sum. These definitions have `Fintype` instances.

`Strip.Polygon N = Bool × Fin (N+1)`, with `false` for top vertices and
`true` for bottom vertices. `Strip.Face N = Fin N × Bool` has these orders:

| Face | Ordered polygon vertices | Source triangle |
|---|---|---|
| `(i,false)` | `(T_(i+1),T_i,B_i)` | `τ_(2i+1)` |
| `(i,true)` | `(B_i,B_(i+1),T_(i+1))` | `τ_(2i+2)` |

The maps `Strip.corner₀`, `corner₁`, and `corner₂` give these vertices.
`Strip.localWeight f p` gives the three barycentric weights there and zero
elsewhere. `Strip.Copy n N = Face N × Triangle.Vertex n` is finite.

`Strip.Glued n N` is the quotient of `Copy n N` by equality of these global
weight functions. `Strip.glue_eq_iff` gives its exact equality criterion.
The classification is proved, rather than assumed:

- `Strip.glue_same_side_iff`: equal-kind copies agree only in the same face
  with the same lattice point.
- `Strip.glue_opposite_iff`: a top face `i` and bottom face `j` agree exactly
  in one of the following two cases:
  \[
  i=j,\quad b=b'=0,\quad a=c',\quad c=a';
  \]
  \[
  i=j+1,\quad a=a'=0,\quad b=c',\quad c=b'.
  \]
  These are precisely the diagonal and vertical shared edges with equal
  weights at their named endpoints.
- `Strip.interior_glue_eq_iff`: an interior point has a unique triangle copy.

Thus the quotient introduces exactly the prescribed edge identifications.
It has a `Fintype` instance. `Strip.weight` is injective, and
`Strip.gluedEquivWeightImage` identifies the quotient with the image of the
concrete polygon weight map.

## Actual boundary omission and matrix entries

`Strip.Boundary v` means that `v` has a representative with `c=0`.
In both displayed face orders this is the actual top or bottom polygon segment.
`Strip.boundary_glue_iff` proves that it is equivalent to `c=0` in any
representative. `Strip.mixed_localWeight_iff` proves that a representative has
positive weight on both polygon sides exactly when `c>0`.

`Strip.Vertex n N` retains precisely those glued vertices with positive weights
on both sides. `Strip.retainedEquivOmitBoundary` is an equivalence with
`{v : Glued n N // ¬ Boundary v}`. No transverse edge is omitted.

`Strip.arrowCount` sums the three oriented arrows over every face and elementary
cell, using their glued endpoints. `Strip.gluedMatrix` is the forward count
minus the reverse count. `Strip.matrix` restricts this matrix to retained
vertices. The following results specify its entries:

| Declaration in `FgStrip.Strip` | Conclusion |
|---|---|
| `matrix_eq_signed_count` | Forward multiplicity minus reverse multiplicity |
| `matrix_eq_sum` | Sum of all oriented elementary cycle contributions |
| `matrix_omitBoundary` | Omission preserves every retained matrix entry |
| `matrix_concrete_entries` | The same signed sum computed with polygon weight vectors |
| `matrix_skew`, `matrix_diag` | Skew symmetry and zero diagonal |

In particular, the weight-image correspondence preserves signed matrix entries.
The matrix counts no assumed arrows or local deletion certificates.

## Edge and interior interfaces

`Triangle.EdgeWeight n = {k : Fin n // 0<k.val}`. Its value is always the
**bottom endpoint weight** on a strip edge. `Strip.EdgeIndex N = Fin (2*N+1)`.
The endpoint maps are

\[
\operatorname{edgeTop}(j)=\lfloor(j+1)/2\rfloor,\qquad
\operatorname{edgeBottom}(j)=\lfloor j/2\rfloor.
\]

`Strip.edge_endpoints_even` and `edge_endpoints_odd` prove the source formulas
`e_(2i)=T_i B_i` and `e_(2i+1)=T_(i+1) B_i`.
`Strip.edgeCopy hN j k` explicitly chooses a triangle representative;
`edgeCopy_weight` proves that it has weight `n-k` at the top endpoint and `k`
at the bottom endpoint, with zero weights elsewhere.

For `hN : 0<N`, the reusable embeddings and sets are:

| Declaration in `FgStrip.Strip` | Interface |
|---|---|
| `faceEmbedding f` | `{p : Triangle.Vertex n // 0<p.c} ↪ Vertex n N` |
| `interiorEmbedding f` | `Triangle.Interior n ↪ Vertex n N` |
| `edgeEmbedding hN j` | `Triangle.EdgeWeight n ↪ Vertex n N` |
| `edgeSet hN j` | `L(e_j)`, the range of the edge embedding |
| `leftEdge N`, `rightEdge N`, `middleEdge N` | Indices `0`, `2*N`, `N` |
| `protectedSet hN` | `P = L(e_0) ∪ L(e_(2N))` |
| `internal hN` | `I = V_strip \ P` |
| `middle hN` | `L(e_N)` |

`Strip.edgeWeight_injective` recovers both the edge index and its weight.
Consequently distinct edge sets are disjoint (`edgeSet_disjoint`), and each
has exactly `n-1` vertices (`card_edgeSet`). The weight formula proves that
both end edges are retained. `interior_ne_edge` separates interiors from all
transverse edges. `interior_mem_internal` places every triangle interior in
`I`; `edgeSet_subset_internal` does the same for each non-end edge.

`Strip.middle_subset_internal` proves `L(e_N) ⊆ I` for every `N>0`.
`middle_endpoints_odd r` identifies the distinguished edge for `N=2*r+1`
as `T_(r+1) B_r`. The definitions do not fix `N=n/2` or require even `N`.
The construction needs only `N>0` for its edge representatives, so all source
parameters `n≥2`, `N≥max(n/2,2)` are covered.

The two-triangle grid, local mutation words, deletion calculations, global
rounds, and the embedded-surface application are proved in separate modules;
this construction does not assume them.
