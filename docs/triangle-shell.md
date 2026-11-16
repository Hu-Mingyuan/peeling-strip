# Triangle-interior shell deletion

The source is proof-blueprint Section 2 and manuscript `main.tex:3575–3654`.

The public module is `FgStrip.TriangleShell`. All new declarations are in
`FgStrip.TriangleShell`, including the sequence helpers. The four foundation
modules `Triangle`, `Strip`, `Mutation` and `Deletion` are its inputs.

## Statement and live sets

`cornerSet p` is exactly the manuscript's `C_p`. `baseLive p` requires

\[
c>0,\qquad p<a+c,\qquad p<b+c,\qquad
(a=0\ \text{or}\ b=0)\Longrightarrow c+p<n.
\]

`baseLive_iff` identifies this set with omission of `c=0`, deletion of both
other sides to depth `p`, and deletion of `C_p`. Its additional hypothesis
`p<n` follows from the shell theorem's range.

`triangle_interior_shell (hp : 1 ≤ p) (hpn : p ≤ (n-1)/2)` proves a finite
`Sequence` for the concrete `Triangle.matrix n`, supported in `interiorSet n`.
Its final live set is `baseLive p \ cornerSet (p+1)`. It also proves an
`Execution` from the initial restriction to the exact final restriction.
`Execution.cons` passes the actual preceding mutate/delete/reverse output to
the next step. Finally, `shell_deleted_exact` proves

\[
\operatorname{baseLive}(p)\setminus
 (\operatorname{baseLive}(p)\setminus C_{p+1})=C_{p+1}\setminus C_p.
\]

The side depth stays `p`; it is not silently increased to `p+1`.
Each `Sequence.cons` contains a `DeletionMove` from the delivered foundation,
with an interior target and interior pivots. The surviving subtype excludes
the target from both the forward and reverse words. The sign condition ranges
over the entire current live type, including both retained sides.

## Cycle calculation and mutation induction

| Source content | Lean declaration |
|---|---|
| Directed contributions of all elementary cycles | `arrowCount_eq` |
| All six signed directions, including side entries and zero unlisted coefficients | `matrix_eq` |
| Exchange of `a,b` reverses the actual matrix | `exchange`, `matrix_exchange` |
| Original complete interior expression | `matrix_interior_row` |
| Indicators of the possibly absent `A_b,B_b` | `off` |
| Complete original path rows on the explicit live set | `linePath_original_row` |
| Actual listed path mutation prefix | `pathWord`, `path_prefix_row` |
| Final path endpoint expression | `path_final_row`, `first_final_row` |
| Concrete word in the surviving subtype | `firstWord`, `firstWord_map`, `first_word_avoids` |
| Rank-three zero expression | `rank_three_row` |
| Concrete first-family move | `firstMove` |
| Exact next first-family live set | `firstMove_liveSet` |
| First family, decreasing `a` | `first_sequence` |
| Exchanged move after the first family | `second_move`, `second_sequence` |
| Unique overlap and skipped endpoint | `shell_overlap`, `second_start` |
| Complete shell sequence | `shell_deletion`, `triangle_interior_shell` |
| Actual output and successive execution | `stepOutput`, `stepOutput_original`, `Sequence.execution` |

`arrowCount_eq` splits the cell sum into its three arrows. Each arrow's source
map is injective. Its possible cell is constructed from the coordinates, so
the indicator is derived from the sum rather than assumed.

The mutation argument uses the original complete expressions. In zero-based
path indices, let `v i=(a,i+1,n-a-i-1)`, `m=n-p-2`, and
`f i=off a i`. Before any mutation,

\[
B(v_i,j)=f_i(j)-\mathbf1_{i<m}f_{i+1}(j)
 +\mathbf1_{i<m}\delta_{v_{i+1},j}
 -\mathbf1_{0<i}\delta_{v_{i-1},j}.
\]

After the first `t` pivots, for `t≤k≤m`, `path_prefix_row` proves

\[
B_t(v_k,j)=B(v_k,j)+
 \mathbf1_{k=t,\,t>0}\bigl(2\delta_{v_{k-1},j}-f_k(j)\bigr).
\]

The proof substitutes `FgStrip.mutate`. The negative part of the next pivot
expression is `f_(t+1)`. More distant path rows have zero coefficient at that
pivot. The endpoint therefore has the complete expression
`δ(v_(m-1))`, including zero coefficients at every other live vertex.
The hypotheses of this algebraic lemma are proved for the concrete matrix by
`linePath_original_row`, `off_nonneg`, `off_line_zero`, and `off_disjoint`.
No pivot or deletion certificate is an input to the shell theorem.

Absent first-pivot neighbours are covered by their zero indicators. The proofs
`off_endpoint_zero`, `onLine_after_zero`, and `onLine_zero_zero` derive the
missing labels from the live-set inequalities. For `n=3,p=1`, the live type
has just the interior vertex, its matrix entry is zero by skew symmetry,
and the word is empty. No finite enumeration or native evaluation is used.

For the second family, `secondMap` reflects into the first-family live set.
`pullMove` restricts the checked move along this injection, and
`matrix_exchange` accounts for the reversed arrows. The upper index is
`min p (n-p-2)`. It equals `p-1` when `n=2p+1`, which skips the already
deleted `(p,p,1)`. All required second-family pivots survive the first family.

## Integration interfaces

`Sequence A I U T` is a finite inductive sequence of supported concrete moves.
`Sequence.trans` composes sequences on a common explicit live set.
`Sequence.subset` and `Sequence.deleted_interior` prove `T⊆U` and `U\T⊆I`.
`Sequence.execution` proves execution from `A|U` to `A|T` using deletion undo.
These helpers are namespaced here and do not change the foundation modules.

`pullMove d f hf s hs hW` constructs a move after any injective restriction
that retains its target and every pivot. It returns the exact target and the
mapped word equality. The deleted set outside that word is arbitrary.

`extendMatrix B` extends a matrix to `V ⊕ F` by zero, for an arbitrary exterior
type `F`. `validDeletionWord_ambient` adds any skew `E` whose target and pivot
rows vanish. `validDeletionWord_ambient_restrict` also permits any further
injective restriction retaining the target and word. Its sign test includes
all retained exterior vertices. These lemmas reuse the delivered mutation,
restriction, and additive transport algebra.

`firstWord_ambient` supplies the concrete first-family instance. Its only
ambient hypothesis, besides skew symmetry, is zero `E` rows at every interior
local vertex. Its complementary block, including both side-to-exterior and
side-to-side entries, is unrestricted. `second_move` supplies a concrete
supported move to the same generic transport theorem for the exchanged family.
`Sequence.add` and `triangle_interior_shell_add` preserve the entire shell
execution under skew additions on the original triangle index type.

Full strip rounds, two-triangle geometry, and the surface application are
proved in separate modules.
