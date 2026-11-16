# Mutation and deletion foundations

This implements target-theorem Section 2, equations (3)–(5), and the ambient
calculation in proof-blueprint Section 1. The manuscript source is
`main.tex:3368–3409`.

All declarations below are in namespace `FgStrip`. The matrix type is
`Matrix V V ℤ`. The identities are entrywise and hold for arbitrary vertex
types with decidable equality, hence in particular for every finite vertex type.

| Content | Declaration |
| --- | --- |
| Entrywise skew symmetry | `SkewSymmetric` |
| Positive part `max a 0`; exact signed correction | `posPart`, `mutationTerm` |
| Mutation; entries incident to and away from the pivot | `mutate`, `mutate_row`, `mutate_col`, `mutate_of_ne` |
| Skew symmetry preserved | `SkewSymmetric.mutate`, `SkewSymmetric.mutateWord` |
| Mutation involution | `mutate_involutive` |
| Restriction using `Matrix.submatrix` | `restrictMatrix`, `restrictMatrix_comp`, `SkewSymmetric.restrictMatrix` |
| Injective restriction commutes with mutation | `restrictMatrix_mutate`, `restrictMatrix_mutateWord` |
| Reindexing by equivalence | `reindex_mutateWord` |
| Listed-order word, concatenation, inverse | `mutateWord`, `mutateWord_cons`, `mutateWord_append`, `mutateWord_reverse` |
| Arrow reversal | `mutate_neg`, `mutateWord_neg`, `SourceOrSink.neg`, `ValidDeletionWord.neg` |
| Zero pivot row implies zero column | `SkewSymmetric.col_zero` |
| Arbitrary additive complementary block | `mutate_add_of_row_zero`, `mutateWord_add_of_rows_zero`, `mutateWord_add_of_support` |
| Full row sign conditions | `IsSource`, `IsSink`, `SourceOrSink`, `ValidDeletionWord` |
| Surviving vertex type | `Remaining` |
| Actual mutate/delete/reverse operation | `deletionUndo` |
| Exact output after deletion and undo | `deletionUndo_eq_restrict`, `restriction_undo` |
| Complete deletion row preserved by ambient addition | `mutateWord_add_row`, `validDeletionWord_add_iff` |
| Validity after additional deletions | `SourceOrSink.restrictMatrix`, `mapRemaining`, `validDeletionWord_restrict` |
| Move on explicit live subset `U` | `DeletionMove` |
| Live pivots, final subset, its identification | `DeletionMove.pivot_live`, `DeletionMove.liveSet`, `DeletionMove.remainingEquiv` |
| Move output and original ambient entries | `DeletionMove.output`, `DeletionMove.output_eq_restrict`, `DeletionMove.output_skew`, `DeletionMove.output_original` |
| Empty-word and arrow-reversed moves | `DeletionMove.ofSourceOrSink`, `DeletionMove.neg` |

`mutateWord B [k₁, k₂] = mutate (mutate B k₁) k₂`.
The word reversal theorem follows by induction using single-pivot involution.
Restriction commutes with a word whose pivots are in the retained index type.
Applying these two equalities proves `deletionUndo_eq_restrict`. Neither
involution nor undo needs skew symmetry or a source/sink hypothesis.

A `DeletionMove U B` has `vertex : U` and
`word : List {v : U // v ≠ vertex}`. Thus every forward and reverse pivot
is live and differs from the deletion vertex. Its `source_or_sink` field is
exactly the disjunction of the two signs, each quantified over **all** `v : U`.
The output is defined by mutation, restriction, and the reversed word.
Its equality with restriction is a theorem, not an input field.
Skew symmetry of the input implies skew symmetry of the output.
The nested surviving type is canonically equivalent to
`{v : V // v ∈ U ∧ v ≠ vertex.val}` by `remainingEquiv`.

For an additive skew matrix `E`, `mutateWord_add_of_support` assumes only
`E k j = 0` for `k ∈ I` and every ambient `j`, with all word pivots in `I`.
It concludes `mutateWord (B + E) W = mutateWord B W + E`.
There is no hypothesis on `E` restricted to the complement of `I`.
Transporting a deletion condition additionally requires `E s j = 0` for
the deletion vertex `s` and every ambient `j`; this is explicit in
`validDeletionWord_add_iff`. No protected or exterior coefficient is omitted.

The pinned mathlib sources were searched for matrix/quiver mutation,
Fomin–Zelevinsky, and skew-symmetry interfaces. No matching mutation result was
found. The implementation reuses `Matrix.submatrix`, list operations, and
kernel-checked ring identities. It does not use native evaluation.

This module proves general algebra. It neither assumes nor proves existence
of the strip deletion words or the main theorem. The strip construction, local
row calculations and global rounds are proved in separate modules.
