# Common-edge deletion

Import `FgStrip.CommonEdge`.

The source is proof-blueprint Sections 3–5 and manuscript `main.tex:3860–3980`
(`lem:edge-layer`).

## Implementation

Names below have prefix `FgStrip.CommonEdge`.

`live p` deletes exactly `deletedEdge p`, `CX (p+1)`, and `CY (p+1)`.
`mem_live_iff` expresses the same live set by coordinate inequalities.
`support n = {u | 0<u.i ∧ u.i<n}` excludes both interface edges.
`endpoints p` contains the two required diagonal indices, counting equality
once. `finish p = live p \ endpoints p` and `deleted_exact` identify the exact
required deletion. `live_halfturn` proves invariance of the initial live set.

`wordLive p false = live p`. `wordLive p true` additionally removes `D_(p+1)`.
`pivotRegion` distinguishes the ordinary and modified diagonal ranges and the
common lower-triangle range. `pivot_live`, `pivot_supported`, and `pivot_avoids`
prove survival, support, and target avoidance for those ranges.
`diagonalWord`, `columnWord`, `columnsWord`, and `forwardWord` implement the
listed diagonal and column orders on these actual live subtypes.

## Public interface

All variables below are unrestricted natural numbers. The hypothesis
`p < n/2` is exactly the manuscript's `p < floor(n/2)`; it implies
`2*p+2 ≤ n`. There is no assumed deletion certificate.

```lean
common_edge_sequence {n p : ℕ} (hp : p < n/2) :
  TriangleShell.Sequence (TwoTriangle.matrix n) (support n) (live p) (finish p)

common_edge_deletion {n p : ℕ} (hp : p < n/2) :
  TriangleShell.Sequence (TwoTriangle.matrix n) (support n) (live p) (finish p) ∧
  TriangleShell.Execution (support n)
    (restrictMatrix (TwoTriangle.matrix n) (Subtype.val : live p → TwoTriangle.Grid n))
    (restrictMatrix (TwoTriangle.matrix n) (Subtype.val : finish p → TwoTriangle.Grid n)) ∧
  live (n := n) p \ finish p = endpoints p
```

`Sequence` is the checked TriangleShell inductive sequence of actual
`DeletionMove`s. `Sequence.execution` links each step to the actual
mutate/delete/reverse output via `DeletionMove.output_original`. Thus the output
is the original matrix on precisely the final live set.

```lean
forwardMove {n p : ℕ} (hn : 2*p+3 ≤ n) (b : Bool) :
  DeletionMove (wordLive (n := n) p b)
    (restrictMatrix (TwoTriangle.matrix n) Subtype.val)
```

Its target is `D_(n-p-1)`. Its word is `deletionWord hn b`; the `Remaining`
subtype enforces avoidance of the target. `forwardWord_supported` and
`deletionWord_supported` place every pivot in `support n`.
`forwardMove_supported` gives the same fact for the deletion vertex.
The sign proof `forward_sink` quantifies over every vertex of `wordLive p b`.

## Concrete mutation calculation

Write `r=p+2` and `t=n-p-1`. The indicator `e i j v` is one exactly at the
coordinate `(i,j)`, and zero elsewhere. An absent label therefore contributes
zero without adding a vertex to the grid or live set.

`diagonal_row` and `lower_row` expand `TwoTriangle.matrix_formula`, whose arrows
were proved from the concrete cycles. `top_diagonal_correction` evaluates
`rowCorrection` directly from `FgStrip.mutate` and its positive-part formula.
`independent_word_row` proves how mutually disconnected diagonal pivots combine.
The interval summed by `top_after_diagonal_interval` begins at

```lean
start (p := p) false = p+1
start (p := p) true  = p+2
```

Thus the modified calculation excludes the absent first pivot before mutation.
It is not obtained by restricting a word containing that pivot.
`top_after_diagonal` and `lower_after_diagonal` give the initial complete
expressions. `SweepState` records the target row and every future pivot row on
**all** live columns. `sweep_entry`, `pivot_parts`, `sweep_step`, and `target_step`
prove the actual one-pivot updates. `SweepState.column_prefix`,
`SweepState.column`, `SweepState.next`, and `prefix_ready` induct through the
actual lists in `forwardWord`.

The final expression has the exact signature:

```lean
forward_target_row {n p : ℕ} (hn : 2*p+3 ≤ n) (b : Bool)
    (v : wordLive (n := n) p b) :
  mutateWord (restrictMatrix (TwoTriangle.matrix n) Subtype.val)
      (forwardWord hn b) (target hn b) v =
    -e (n-p-1) 1 v.val -
      (if b=true ∧ p+2=n-p-1 then e (n-p-2) (n-p-1) v.val else 0)
```

For the ordinary word, and for the modified word with `r<t`, the row is
`-e t 1`. For the modified word with `r=t` (`n=2*p+3`), it is
`-e t 1-e (t-1) t`, as required. `anchor`, `pivotPos`, and `pivotNeg` also encode
the corresponding modified intermediate expressions.

`coincident_sequence` treats `n=2*p+2` by one empty-word deletion at the sink.
`first_sequence` uses the ordinary word. `second_move` transports the separately
calculated modified word through `H`, using `matrix_halfturn` and `pullMove`.
`secondMap` and `secondLift` identify the once-deleted live set, so both endpoint
deletions are counted exactly once. `distinct_sequence` composes these moves.
No positivity assumption on `p` occurs. `e_zero_bottom`,
`first_column_left_zero`, `target_upper_zero`, and `omitted_diagonal_zero`
handle the absent labels, including `p=0`.

| Source location | Checked declarations |
| --- | --- |
| `main.tex:3860–3878`, coincident endpoint and local scope | `coincident_row`, `coincident_sequence`, `common_edge_sequence` |
| `eq:pruned-word`, live pivots and support | `diagonalWord`, `columnsWord`, `deletionWord`, `forwardWord_region`, `deletionWord_supported` |
| `eq:pruned-top`, `eq:pruned-last` | `diagonal_zero`, `top_diagonal_correction`, `top_after_diagonal_interval`, `top_after_diagonal` |
| `eq:pruned-lower` and its verification | `lower_row`, `lower_after_diagonal`, `sweep_step`, `SweepState.step` |
| target row and `eq:pruned-final` | `target_after_diagonal`, `target_step`, `forward_target_row`, `forward_sink` |
| omitted first pivot and the separate `r=t` calculation | `start`, `wordLive`, `anchor`, `pivotPos`, `top_after_diagonal_interval`, `forward_target_row` with `b=true` |
| final half-turn and induced subquiver | `second_move`, `distinct_sequence`, `common_edge_deletion` |

## Interfaces, reversal and ambient attachment

`sequence_restrict` applies to any supported sequence and any set disjoint from
its support. `interface_disjoint` supplies this hypothesis for arbitrary further
L/R deletions. The exported `common_edge_restrict` consequently retains every
target and pivot. `sequence_neg` and `common_edge_reverse` reverse all arrows.

`ambientLive U` consists of local vertices in `U` and **all** exterior vertices
of an arbitrary type `Z`. `ambientSupport I` contains only the local support.
`sequence_extend` reuses `validDeletionWord_ambient_restrict`; `sequence_ambient`
then uses `Sequence.add`. Its hypothesis is only

```lean
SkewSymmetric E
∀ u ∈ I, ∀ z, E (Sum.inl u) z = 0
```

The exported `common_edge_ambient` and `common_edge_reverse_ambient` return both
`Sequence` and `Execution`, from `ambientLive (live p \ F)` to
`ambientLive (finish p \ F)`. Their matrix is `extendMatrix (matrix n)+E`, or
`extendMatrix (-matrix n)+E` for reversed orientation. Entries between interface
vertices, between interfaces and exterior vertices, and within the exterior
block are unrestricted. They persist as entries of the same original matrix
in the final restriction.
No global-round hypothesis enters the local theorem.
