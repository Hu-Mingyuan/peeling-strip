# Main theorem: deleting the middle edge

The source is manuscript `main.tex:4119–4161`, together with both PDFs and
their TeX sources.

## Verification status

The public theorems are `FgStrip.Proposition74.ambient` and
`FgStrip.Proposition74.triangulation`. `scripts/verify.py` builds every module
and checks fresh consumers of both statements.

The consumer `verification/Proposition74Consumer64317868.lean` checks the full
ambient statement and prints 133 transitive axiom reports. Every report uses
only `propext`, `Classical.choice` and `Quot.sound`; eight declarations use no
axioms. The reports include both final theorems, every new integration
declaration, and the local shell, common-edge, gluing and incidence results
used by the integration. Each `#print axioms` includes transitive dependencies.

## Statement and source map

Names below denote checked declarations. An unqualified name in a table row
uses the namespace of the preceding qualified name.

`FgStrip.Proposition74.ambient` has hypotheses
`2 ≤ n`, `max (n/2) 2 ≤ N`, a finite ambient type `V` with decidable equality,
an injection `i : Strip.Vertex n N ↪ V`, and an integer matrix `E` with

```lean
SkewSymmetric E
∀ x ∈ Strip.internal hN, ∀ v, E (i x) v = 0
```

There is no condition on the complementary block of `E`. In particular, its
protected/protected, protected/exterior and exterior/exterior entries are arbitrary.
Decidable equality is only a representation choice and can be supplied classically.
The transport construction itself does not require ambient finiteness.
The conclusion supplies a set `Z`, the two inclusions
`i '' Strip.middle hN ⊆ Z ⊆ i '' Strip.internal hN`, a supported `Sequence`
from `Set.univ` to `Zᶜ`, and an actual `Execution` ending at the restriction of
`zeroExtension i (Strip.matrix n N) + E` to `Zᶜ`.
Every move contains a word in `Remaining d.vertex`; its source/sink condition
quantifies over the entire live subtype. `Sequence.execution` identifies the
successive actual mutate/delete/reverse outputs with those restrictions.

`FgStrip.Proposition74.triangulation` applies the ambient theorem to
`AmbientTriangulation.Data.matrix`. Its only additional geometric premises are
`Data.BoundaryCompatible` and `Data.FaceIncidence`.
`Data.ambient_hypothesis` supplies the matrix split, exterior skew symmetry and
zero rows. Neither theorem takes a deletion certificate or an assumed target.
The application allows any extra polygon-vertex type `X` and finite outside-face
type `O`. Its geometric conditions are exactly

```lean
∀ f p, d.Omitted (extendWeight (Strip.localWeight f p)) ↔ p.c = 0

∀ o p f q,
  d.localWeight (Sum.inr o) p = extendWeight (Strip.localWeight f q) →
    q.c = 0 ∨ ∃ j k,
      (j = Strip.leftEdge N ∨ j = Strip.rightEdge N) ∧
      Strip.localWeight f q = Strip.edgeWeight j k
```

The injection `d.embedding hb` is constructed by the delivered gluing theorem.
There is no additional equality assumption on the entire induced strip matrix.

| Source | Implemented declarations |
| --- | --- |
| Glued FG construction, `main.tex:3134–3151` | `Strip.Vertex`, `Strip.matrix`, `Strip.matrix_concrete_entries`, `Strip.faceEmbedding`, `Strip.edgeEmbedding`; existing `docs/strip-construction.md` |
| Local shell, `3575–3654` | `TriangleShell.shell_deletion`; `Rounds.retained_shell_sequence`, `face_contribution_extension`, `face_supported_rows`, `shell_sequence_on_live` |
| Pair identifications, `3767–3792` | `TwoTriangle.Pair.embedding`, `contribution_eq`, `strip_row_eq_contribution`; `Rounds.pair_contribution_extension`, `pair_supported_rows` |
| Common edge, `3860–3980` | `CommonEdge.common_edge_sequence`, `common_edge_restrict`, `common_edge_reverse`; `Rounds.pair_local_sequence`, `pair_sequence_on_live` |
| Exact live sets | `Rounds.profileLive`, `roundLive`, `profile_pair_preimage`, `profile_face_preimage`, `profile_edge_update`, `profile_face_update` |
| Global rounds, `4119–4161` | `Rounds.batch_faces`, `batch_edges`, `first_round`, `next_round`, `rounds` |
| Terminal edge and protected ends | `Rounds.middle_not_mem_roundLive`, `protected_mem_roundLive`; `Proposition74.strip` |
| Arbitrary injection and complementary block | `Rounds.sequence_equiv`, `sequence_injection`, `sequence_on_live`, `sequence_of_rows`; `Proposition74.ambient` |
| Explicit ambient triangles | `Proposition74.triangulation`, `AmbientTriangulation.Data.ambient_hypothesis` |

The exact depth functions are

```lean
edgeDepth N p j = min p (min j (2*N-j))
faceDepth N p i = min p (min i (2*N-i+1))
```

`profileLive` states the live inequalities at every embedded edge point and
excludes the stated corner set at every embedded interior point.
`profileLive_edge` and `profileLive_interior` prove these conditions are exact,
using the injectivity and disjointness of the glued embeddings.

Each round composes a finite set of independent shell moves, then a finite set
of common-edge moves. The finite-set induction need not prescribe increasing
edge order. At every intermediate step, previously processed neighbours merely
increase the interface depth. `pairExtra` and `profile_pair_preimage` identify
these extra deletions explicitly. All local words avoid the interfaces.
This is an alternative ordering of the same source moves, not a changed target.

The first round uses `C_1=∅` directly. For ranks two and three this is the only
round. Pair orientation is selected by the checked `Pair` construction.
Middle-edge removal uses its index `N` and does not assume `N` is even.

## Reproduction

The Lean and mathlib pins are `v4.34.1` and
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Run

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

Existing nonfatal linter warnings do not affect the kernel checks.
No finite computation substitutes for the quantified theorem.

No source-proof correction was found. The finite-set ordering of independent
moves is the implementation difference described above. Elaboration repairs
changed coercions, explicit parameters and library lemma names; they did not
alter any mathematical hypothesis or conclusion.
