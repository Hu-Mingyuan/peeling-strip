# Peeling strip

Lean formalization of Proposition 2.7 of *Ice and mirrors* ([arXiv:2611.21484](https://arxiv.org/abs/2611.21484)). For every rank `n ≥ 2` and strip length `N ≥ max (n / 2) 2`, a finite sequence of supported deletion moves removes every lattice vertex on the middle edge `e_N`. No vertex on the two end edges is mutated or deleted. The resulting matrix is the full induced submatrix of the original matrix.

This repository contains a combinatorial quiver theorem, not a formalization of homological mirror symmetry. No GitHub Pages deployment is configured.

## The theorem

The main declaration is [`FgStrip.Proposition74.ambient`](FgStrip/Proposition74.lean). The strip matrix is constructed from the oriented FG triangle cycles, with shared edge vertices identified and actual boundary vertices omitted. Positive matrix entries denote outgoing arrows.

Let `i : Strip.Vertex n N ↪ V` embed the strip vertices in an arbitrary finite ambient vertex set. The ambient matrix is `zeroExtension i (Strip.matrix n N) + E`, where `E` is any skew-symmetric integer matrix whose rows vanish at every nonprotected strip vertex. The complementary block is unrestricted. It can contain arrows between protected end-edge vertices, between those vertices and exterior vertices, and between exterior vertices.

The theorem produces a deleted set `Z` containing the image of the middle edge and contained in the image of the strip interior. It supplies both a supported `Sequence` and an `Execution` whose final matrix is exactly the restriction of the original ambient matrix to `Zᶜ`. The source or sink condition is tested on the entire current ambient vertex set. A deletion move mutates a word avoiding the vertex to be deleted, deletes that source or sink, and applies the reversed word.

`FgStrip.Proposition74.triangulation` applies the theorem to an actual sum of embedded triangle contributions. Its hypotheses `BoundaryCompatible` and `FaceIncidence` state which lattice points are omitted on the boundary and how exterior triangles meet the strip. They imply the matrix extension hypothesis; they do not assume a deletion sequence. This is a combinatorial triangle-incidence model, not a formalization of topological surfaces.

The argument includes odd and even `N`, both endpoint deletions, the omitted first mutation in the second word, and the coincident-endpoint case. It is universally quantified; the finite Python checks are supplementary only.

## Read the mathematics

- [Target theorem](target-theorem.pdf) and [proof blueprint](proof-blueprint.pdf), with editable sources in [docs/tex](docs/tex).
- [Final proof correspondence](docs/main-theorem.md) and [ambient triangulation construction](docs/ambient-triangulation.md).
- [Independent statement review](verification/statement-review.md) and [reproducible verification receipt](verification/publication-check.json).

| Blueprint part | Lean modules |
| --- | --- |
| Matrix mutation, restriction, and deletion/undo | `FgStrip/Mutation.lean`, `FgStrip/Deletion.lean` |
| FG triangle cycles and glued strip | `FgStrip/Triangle.lean`, `FgStrip/Strip.lean` |
| Triangle-interior shell deletion | `FgStrip/TriangleShell.lean` and its supporting modules |
| Two-triangle coordinates | `FgStrip/TwoTriangle.lean` and its supporting modules |
| Common-edge deletion and the second endpoint | `FgStrip/CommonEdge.lean` and its supporting modules |
| Arbitrary strip length and round induction | `FgStrip/Rounds.lean` and its supporting modules |
| Ambient application and final theorem | `FgStrip/AmbientTriangulation.lean`, `FgStrip/Proposition74.lean` |

The mathematical source is Proposition 2.7 of *Ice and mirrors* ([arXiv:2611.21484](https://arxiv.org/abs/2611.21484)). The Lean declarations are named `Proposition74`; this is Proposition 2.7 in the arXiv version. The accepted library source hashes are recorded in [accepted-library.json](verification/accepted-library.json).

## Reproduce the checks

Use Linux or Ubuntu under WSL, with Elan, Git, Python 3, and Bash 4 or newer.

```sh
git clone https://github.com/Hu-Mingyuan/peeling-strip.git
cd peeling-strip
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The verifier checks the pinned dependency revisions and clean dependency worktrees, builds every project module, and checks fresh consumers of both final theorem statements. It audits every declaration attributed to every project module, including private and generated declarations, and the final theorem roots. The only permitted transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The verifier also checks that the library matches its accepted source hashes and that all verification inputs remain unchanged. It writes `verification/publication-check.json` and the matching logs. A successful run ends with `FG_STRIP_PROPOSITION74_VERIFIED`. The [GitHub Actions workflow](.github/workflows/lean.yml) runs the same commands.

| Dependency | Pinned revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

Mathlib is the sole direct package requirement. No dependency source is modified or vendored here.
