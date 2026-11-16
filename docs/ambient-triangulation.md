# Ambient triangle decomposition

`FgStrip.AmbientTriangulation.Data.ambient_hypothesis` proves

\[
 B=B_{\mathrm{strip,ext}}+E,\qquad E_{uv}=-E_{vu},\qquad
 E_{\iota(x),v}=0\quad(x\in I,\ v\in V).
\]

Here `B` is the signed cycle sum of the ambient triangles, followed by actual
boundary omission. The matrix is not defined as `B_strip_ext + E`.
The theorem supplies the independent combinatorial prerequisite in
`target-theorem.pdf`, Section 3, and `proof-blueprint.pdf`, Section 7.
The manuscript correspondence is `main.tex`, lines 3134–3151 and 3368–3409.

## Triangle data and hypotheses

All names below are in `FgStrip.AmbientTriangulation`, unless qualified otherwise.
Choose finite types `X` of extra polygon vertices and `O` of outside faces.
`Data N X O` contains the three ordered corners of each outside face, their
pairwise distinctness, and designated boundary sides of every face.
The polygon vertices and faces are respectively

```lean
Strip.Polygon N ⊕ X
Strip.Face N ⊕ O
```

The strip faces have exactly the ordered corners `Strip.corner₀`, `corner₁`,
`corner₂`, included by `Sum.inl`. Thus they are
`(T_(i+1),T_i,B_i)` and `(B_i,B_(i+1),T_(i+1))`.
No matrix data occur in `Data`.

`d.localWeight f p` places `p.a,p.b,p.c` at the three corners and zero elsewhere.
`d.Glued n` is the finite image of these weight functions. `d.glue_eq_iff` gives
its exact equality criterion. `d.quotientEquiv` identifies it with the literal
quotient of face copies by equal weights. `d.localWeight_injective` proves that
no face identifies its own distinct lattice points. Finiteness of the lattice
uses only finiteness of `O`, so the theorem also permits an infinite supply of
unused extra polygon labels.

A marked side `k : Fin 3` is opposite corner `k`. `coordinate p k = 0` means
that `p` lies on it. `d.Omitted` consists of all glued points represented on
marked sides. `d.Vertex n` retains precisely the complement.
`d.retainedFaceEmbedding` supplies each retained local-point map.

The hypotheses are finite lattice incidence conditions:

```lean
d.BoundaryCompatible n :=
  ∀ (f : Strip.Face N) (p : Triangle.Vertex n),
    d.Omitted (n := n) (extendWeight (Strip.localWeight f p)) ↔ p.c = 0

d.FaceIncidence n :=
  ∀ (o : O) (p : Triangle.Vertex n) (f : Strip.Face N) (q : Triangle.Vertex n),
    d.localWeight (Sum.inr o) p = extendWeight (Strip.localWeight f q) →
      q.c = 0 ∨ ∃ (j : Strip.EdgeIndex N) (k : Triangle.EdgeWeight n),
        (j = Strip.leftEdge N ∨ j = Strip.rightEdge N) ∧
        Strip.localWeight f q = Strip.edgeWeight j k
```

The first condition says exactly which strip points are on designated actual
boundary segments. In both ordered strip faces, `c=0` is the top or bottom
segment. It excludes an additional boundary designation that would remove a
retained strip point. The second condition allows intersections on those
omitted segments or on either end edge, with matching endpoint weights.
Both can be checked from finite face, side, and lattice data; neither mentions
matrix entries, zero rows, mutation, or deletion.

## Gluing and matrix correspondence

`d.stripGlued` extends strip weights by zero on `X`.
`d.stripGlued_injective` and `d.strip_glue_eq_iff` prove preservation and reflection
of all identifications. In particular, the complete equal-endpoint-weight
classification in `Strip.glue_same_side_iff` and `Strip.glue_opposite_iff` applies
unchanged. Distinct retained strip points cannot become identified.

`d.embedding hb : Strip.Vertex n N ↪ d.Vertex n` restricts this injection after
omission. `d.embedding_face` identifies each actual ordered face embedding.
`d.embedding_edge_weight` gives `n-k` at the named top endpoint and `k` at the
bottom endpoint, including the protected end edges. `d.omitted_stripGlued_iff`
proves exact agreement with `Strip.Boundary`.

`d.matrix n` sums `Triangle.cycleEntry` over every face and `Triangle.Cell n`.
The three vertices of each cell are the source cycle
`(a+1,b+1,c) → (a,b+1,c+1) → (a+1,b,c+1) → (a+1,b+1,c)`.
Restriction to `d.Vertex n` removes the incident arrows of omitted points.
`d.stripContribution n` and `d.exterior n` are the sums over strip and outside
faces respectively. `d.matrix_split` partitions the original face sum.

| Declaration | Proof content |
|---|---|
| `Data.stripContribution_embedding` | Strip entries agree via injective extension of global weights and `Strip.matrix_concrete_entries` |
| `Data.mem_range_of_strip_weight` | A retained point of a strip face belongs to the embedded retained strip |
| `Data.stripContribution_row_zero` | Every strip cycle vanishes outside the strip image |
| `Data.stripContribution_eq_zeroExtension` | The whole strip summand is the zero extension, including all exterior columns |
| `Data.outside_ne_internal` | Face incidence excludes every outside lattice point from the embedded internal strip |
| `cycleEntry_row_zero` | The six signed arrow indicators vanish when the row point differs from all three cycle vertices |
| `Data.exterior_row_zero` | Sum this elementary vanishing over outside faces and cells, for every ambient column |
| `Data.exterior_skew`, `Data.matrix_skew` | Skew symmetry follows directly from the signed elementary cycles |
| `Data.ambient_hypothesis` | The three required ambient conclusions together |

The complement of `ι(I)` has no zero-entry hypothesis. Contributions between
protected vertices, between protected and exterior vertices, and between
exterior vertices are retained in `d.exterior n`. Equality of the full induced
strip matrix with `Strip.matrix` is not asserted.

## Public signatures

```lean
Data.embedding {n N : ℕ} {X O : Type*} (d : Data N X O)
  (hb : d.BoundaryCompatible n) : Strip.Vertex n N ↪ d.Vertex n

Data.stripContribution_eq_zeroExtension {n N : ℕ} {X O : Type*}
  (d : Data N X O) (hb : d.BoundaryCompatible n) :
  d.stripContribution n = zeroExtension (d.embedding hb) (Strip.matrix n N)

Data.exterior_row_zero {n N : ℕ} {X O : Type*} (d : Data N X O) [Fintype O]
  (hb : d.BoundaryCompatible n) (hi : d.FaceIncidence n) (hN : 0 < N)
  (x : Strip.Vertex n N) (hx : x ∈ Strip.internal hN) (v : d.Vertex n) :
  d.exterior n (d.embedding hb x) v = 0

Data.ambient_hypothesis {n N : ℕ} {X O : Type*} (d : Data N X O) [Fintype O]
  (hb : d.BoundaryCompatible n) (hi : d.FaceIncidence n) (hN : 0 < N) :
  d.matrix n = zeroExtension (d.embedding hb) (Strip.matrix n N) + d.exterior n ∧
  SkewSymmetric (d.exterior n) ∧
  ∀ x ∈ Strip.internal hN, ∀ v : d.Vertex n,
    d.exterior n (d.embedding hb x) v = 0
```

`zeroExtension_apply`, `zeroExtension_row_zero`, and `zeroExtension_col_zero`
characterize the extension independently of its implementation.
The fresh consumer prints the elaborated signatures and both incidence definitions.

The result needs only `0<N`; it has no restriction on `n` or the parity of `N`.
It therefore covers every required `n≥2`, `N≥max(n/2,2)`, including odd `N`.
For the deletion theorem, take `V := d.Vertex n`,
`ι := d.embedding hb`, `B := d.matrix n`, and `E := d.exterior n`.
The theorem above supplies its ambient matrix assumptions.
No deletion-existence assertion is assumed or proved here.

## Nonvacuous construction

`stripOnly N : Data N Empty Empty` marks precisely side `2` of every strip
face and has no outside faces. `stripOnly_boundaryCompatible` and
`stripOnly_faceIncidence` verify both hypotheses for all `n,N`.
`stripOnly_embedding_surjective` proves that every retained ambient point is
in the embedded strip. `stripOnly_matrix` identifies its matrix with the zero
extension and `stripOnly_exterior` proves `E=0`.
For `n≥2` and `N>0`, `stripOnly_nonempty` supplies a retained point and
`stripOnly_internal_nonempty` supplies an internal point on the middle edge.
The fresh consumer separately instantiates arbitrary odd lengths.
The main theorem permits any finite outside-face set satisfying incidence.
