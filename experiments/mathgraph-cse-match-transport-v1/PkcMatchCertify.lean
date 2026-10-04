/- Replayable manifest for automatic worked-model matching and CSE certification. -/

module

public import RecordedMatchInference
public meta import RecordedMatchInference

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)

namespace PropertyKindCalculus.Experiments.PkcMatchCertify

open CertifiedCseGate
open RecordedCseQualification
open RecordedMatchInference

def inferenceFailureList (failures : List MatchInferenceFailure) : String :=
  "[" ++ String.intercalate ", "
    (failures.map fun failure => "\"" ++ failure.label ++ "\"") ++ "]"

def quotientFailureList (failures : List TapeQuotientClause) : String :=
  "[" ++ String.intercalate ", "
    (failures.map fun failure => "\"" ++ failure.label ++ "\"") ++ "]"

def header : List String := [
  "mathgraph_pkc_automatic_certification: 1",
  "pkc_revision: 6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9",
  "scenario: recorded-worked-model",
  "matcher_policy: dependency-closure",
  "constant_identity: recording-site",
  "optimizer: PropertyKindCalculus.Paradigm.TapeCSE.cseCompact"]

def render : String :=
  match recordRawAndCompact with
  | .error executionError => String.intercalate "\n" (header ++ [
      "status: EXECUTION_ERROR",
      "execution_error: " ++ reprStr executionError])
  | .ok (raw, _, _, _, _, _, _) =>
      match inferWorkedModelMatch (ofTape raw) with
      | .error failures => String.intercalate "\n" (header ++ [
          "status: MATCH_REJECTED",
          "raw_vertices: " ++ toString raw.size,
          "match_failures: " ++ inferenceFailureList failures,
          "authority: none"])
      | .ok inferred =>
          match certifyCse provenance raw inferred.sourceMatch with
          | .rejected rejected => String.intercalate "\n" (header ++ [
              "status: OPTIMIZATION_REJECTED",
              "raw_vertices: " ++ toString raw.size,
              "match_equals_independent_control: " ++
                (if inferred.sourceMatch == rawMatch then "true" else "false"),
              "source_match_accepted: true",
              "optimization_failures: " ++ quotientFailureList rejected.failures,
              "authority: inferred source acceptance only"])
          | .certified certified => String.intercalate "\n" (header ++ [
              "status: CERTIFIED",
              "raw_vertices: " ++ toString raw.size,
              "compacted_vertices: " ++ toString certified.compactTape.size,
              "match_equals_independent_control: " ++
                (if inferred.sourceMatch == rawMatch then "true" else "false"),
              "source_match_accepted: true",
              "match_failures: []",
              "optimization_failures: []",
              "authority:",
              "  inferred_acceptance: InferredWorkedModelMatch.accepted",
              "  optimized_acceptance: CertifiedCse.accepted",
              "  strong_bisimulation: CertifiedCse.strongBisimulation",
              "  weak_bisimulation: CertifiedCse.weakBisimulation",
              "boundary: worked-model matcher; generic matching still requires harvested metadata and realization tables"])

end PropertyKindCalculus.Experiments.PkcMatchCertify

public def main (_args : List String) : IO UInt32 := do
  IO.println PropertyKindCalculus.Experiments.PkcMatchCertify.render
  pure 0
