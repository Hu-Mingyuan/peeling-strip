import FgStrip
import FgStrip.AmbientTriangulation
import FgStrip.AmbientTriangulation.Construction
import FgStrip.AmbientTriangulation.Examples
import FgStrip.AmbientTriangulation.Matrix
import FgStrip.CommonEdge
import FgStrip.CommonEdge.Ambient
import FgStrip.CommonEdge.Coincident
import FgStrip.CommonEdge.Columns
import FgStrip.CommonEdge.Diagonal
import FgStrip.CommonEdge.Geometry
import FgStrip.CommonEdge.Local
import FgStrip.CommonEdge.Mutation
import FgStrip.CommonEdge.Rows
import FgStrip.CommonEdge.State
import FgStrip.CommonEdge.Sweep
import FgStrip.CommonEdge.Top
import FgStrip.CommonEdge.Transport
import FgStrip.CommonEdge.Words
import FgStrip.Deletion
import FgStrip.Mutation
import FgStrip.Proposition74
import FgStrip.Rounds
import FgStrip.Rounds.Batch
import FgStrip.Rounds.FaceGeometry
import FgStrip.Rounds.Induction
import FgStrip.Rounds.Invariant
import FgStrip.Rounds.PairGeometry
import FgStrip.Rounds.PairMatrix
import FgStrip.Rounds.ProfileUpdates
import FgStrip.Rounds.ShellMatrix
import FgStrip.Rounds.Transport
import FgStrip.Strip
import FgStrip.Triangle
import FgStrip.TriangleShell
import FgStrip.TriangleShell.Ambient
import FgStrip.TriangleShell.Cycles
import FgStrip.TriangleShell.Execution
import FgStrip.TriangleShell.Geometry
import FgStrip.TriangleShell.Local
import FgStrip.TriangleShell.Path
import FgStrip.TriangleShell.Sequence
import FgStrip.TriangleShell.Transport
import FgStrip.TwoTriangle
import FgStrip.TwoTriangle.Contribution
import FgStrip.TwoTriangle.Coordinates
import FgStrip.TwoTriangle.Cycles
import FgStrip.TwoTriangle.Edges
import FgStrip.TwoTriangle.Embedding
import FgStrip.TwoTriangle.Entries
import FgStrip.TwoTriangle.Extension
import FgStrip.TwoTriangle.Labels
import Lean.Util.CollectAxioms

#print axioms FgStrip.Proposition74.ambient
#print axioms FgStrip.Proposition74.triangulation
#print axioms FgStrip.Proposition74.strip
#print axioms FgStrip.Rounds.rounds
#print axioms FgStrip.CommonEdge.common_edge_sequence
#print axioms FgStrip.TriangleShell.shell_deletion
#print axioms FgStrip.DeletionMove.output_original
#print axioms FgStrip.AmbientTriangulation.Data.ambient_hypothesis

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `FgStrip,
    `FgStrip.AmbientTriangulation,
    `FgStrip.AmbientTriangulation.Construction,
    `FgStrip.AmbientTriangulation.Examples,
    `FgStrip.AmbientTriangulation.Matrix,
    `FgStrip.CommonEdge,
    `FgStrip.CommonEdge.Ambient,
    `FgStrip.CommonEdge.Coincident,
    `FgStrip.CommonEdge.Columns,
    `FgStrip.CommonEdge.Diagonal,
    `FgStrip.CommonEdge.Geometry,
    `FgStrip.CommonEdge.Local,
    `FgStrip.CommonEdge.Mutation,
    `FgStrip.CommonEdge.Rows,
    `FgStrip.CommonEdge.State,
    `FgStrip.CommonEdge.Sweep,
    `FgStrip.CommonEdge.Top,
    `FgStrip.CommonEdge.Transport,
    `FgStrip.CommonEdge.Words,
    `FgStrip.Deletion,
    `FgStrip.Mutation,
    `FgStrip.Proposition74,
    `FgStrip.Rounds,
    `FgStrip.Rounds.Batch,
    `FgStrip.Rounds.FaceGeometry,
    `FgStrip.Rounds.Induction,
    `FgStrip.Rounds.Invariant,
    `FgStrip.Rounds.PairGeometry,
    `FgStrip.Rounds.PairMatrix,
    `FgStrip.Rounds.ProfileUpdates,
    `FgStrip.Rounds.ShellMatrix,
    `FgStrip.Rounds.Transport,
    `FgStrip.Strip,
    `FgStrip.Triangle,
    `FgStrip.TriangleShell,
    `FgStrip.TriangleShell.Ambient,
    `FgStrip.TriangleShell.Cycles,
    `FgStrip.TriangleShell.Execution,
    `FgStrip.TriangleShell.Geometry,
    `FgStrip.TriangleShell.Local,
    `FgStrip.TriangleShell.Path,
    `FgStrip.TriangleShell.Sequence,
    `FgStrip.TriangleShell.Transport,
    `FgStrip.TwoTriangle,
    `FgStrip.TwoTriangle.Contribution,
    `FgStrip.TwoTriangle.Coordinates,
    `FgStrip.TwoTriangle.Cycles,
    `FgStrip.TwoTriangle.Edges,
    `FgStrip.TwoTriangle.Embedding,
    `FgStrip.TwoTriangle.Entries,
    `FgStrip.TwoTriangle.Extension,
    `FgStrip.TwoTriangle.Labels]
  for moduleName in modules do
    unless env.header.moduleNames.contains moduleName do
      throwError "Project module not imported: {moduleName}"
  let mut counts : Array Nat := Array.replicate modules.size 0
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some i := modules.toList.idxOf? env.header.moduleNames[idx]! then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Forbidden axiom {axiomName} in {name}"
        logInfo m!"AUDIT {name}: {axioms}"
        counts := counts.modify i (· + 1)
        total := total + 1
  for i in [:modules.size] do
    logInfo m!"AUDITED {modules[i]!}: {counts[i]!} declarations"
  logInfo m!"TOTAL_AUDITED: {total}"

