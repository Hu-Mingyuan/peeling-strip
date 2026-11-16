# Independent statement and proof-structure review

Reviewed on 2026-11-14 against the accepted library, whose source hashes are
recorded in `verification/accepted-library.json`, and the two supplied PDFs.
Two independent reviews covered the final statement and the local proof semantics.
Neither found a blocking mathematical defect. Build and axiom results are recorded
separately by `scripts/verify.py`; this review alone is not a build receipt.

## Statement correspondence

`FgStrip.Proposition74.ambient` quantifies over all `n >= 2` and
`N >= max (n / 2) 2`, every finite ambient vertex type and injection, and every
skew integer matrix `E` whose rows at internal strip vertices vanish. Its
complementary block is arbitrary. No deletion certificate, local row identity,
or existence of the desired sequence is assumed.

The strip matrix is the signed sum of the specified FG triangle cycles, glued
by endpoint weights and restricted after boundary omission. The protected edges
are `e_0` and `e_(2N)`; the middle edge is `e_N`, also for odd `N`.

`FgStrip.Proposition74.triangulation` applies the matrix theorem to the explicit
endpoint-weight incidence model. `BoundaryCompatible` identifies the omitted
boundary vertices, and `FaceIncidence` limits intersections with outside faces.
The matrix hypotheses are proved from these conditions. This is the combinatorial
application permitted by the target PDF, not a formalization of the topology of
arbitrary marked surfaces.

## Proof semantics

- `Mutation.lean` uses the standard Fomin--Zelevinsky positive-part formula.
- `Deletion.lean` tests source or sink against every vertex of the current live
  subtype. A move contains an actual vertex, a live word avoiding it, and its sign
  proof. Its output is computed by mutation, deletion and the reversed word.
- `TriangleShell.Sequence` is a finite inductive composition of supported moves.
  `Sequence.execution` proves the relation to actual successive outputs, ending
  at the restriction of the original matrix.
- The triangle-shell path hypotheses are proved for the concrete cycle matrix.
  Rank three and overlapping endpoints are covered.
- The common-edge calculation uses distinct ordinary and modified words. The
  omitted first pivot is handled separately, including the extra negative term
  in the shortest nontrivial case. The final identity covers every live column.
- `Rounds.rounds` proves the arbitrary-parameter induction from the local results.
  Its finite-set batch order differs from the manuscript's increasing edge order;
  compatibility with additional interface deletions justifies that choice.
- Source inspection found no `sorry`, `admit`, custom mathematical axiom, unsafe
  implementation, `implemented_by`, `extern`, or native-evaluation proof shortcut.
