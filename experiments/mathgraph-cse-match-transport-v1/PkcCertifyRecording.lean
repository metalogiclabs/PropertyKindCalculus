/- Deterministic end-to-end certificate manifest for a recorded PKC computation. -/

module

public import RecordedMatchInference
public meta import RecordedMatchInference

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)

namespace PropertyKindCalculus.Experiments.PkcCertifyRecording

open CertifiedCseGate
open MatchInferenceCore
open RecordedCseQualification
open RecordedMatchInference

def boolText (value : Bool) : String := if value then "true" else "false"

def warrantText : WarrantStatus → String
  | .warrantedBounded => "WARRANTED_BOUNDED"
  | .unknown => "UNKNOWN"
  | .rejected => "REJECTED"

def matchClauseList (failures : List MatchAcceptanceClause) : String :=
  "[" ++ String.intercalate ", "
    (failures.map fun failure => "\"" ++ failure.label ++ "\"") ++ "]"

def quotientClauseList (failures : List TapeQuotientClause) : String :=
  "[" ++ String.intercalate ", "
    (failures.map fun failure => "\"" ++ failure.label ++ "\"") ++ "]"

def ambiguityKindText : AmbiguityKind → String
  | .componentOwnership => "component-ownership"
  | .occurrenceBoundary => "occurrence-boundary"
  | .operationOwnership => "operation-ownership"

def separatorText : Option AmbiguitySeparator → String
  | none => "none"
  | some separator =>
      ambiguityKindText separator.kind ++ "@" ++ toString separator.index

def header : List String := [
  "mathgraph_pkc_recording_certification: 2",
  "pkc_revision: 6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9",
  "scenario: recorded-worked-model",
  "available_match_outcomes: [INFERRED, AMBIGUOUS, REJECTED]"]

def semanticBoundary : List String := [
  "semantic_seal:",
  "  theorem: PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal",
  "  status: OBLIGATIONS_REMAIN",
  "  discharged:",
  "    provenance_well_formed: true",
  "    match_accepted: true",
  "  remaining:",
  "    - recorded_tape_well_formed",
  "    - selected_output_component",
  "    - successful_evaluation_pair",
  "  denotation_bridge:",
  "    theorem: PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal_of_denotes",
  "    status: OBLIGATIONS_REMAIN",
  "    remaining: [carrier_denotation]",
  "policy_result:",
  "  dependency_closure: WARRANTED_BOUNDED",
  "  explicit_recorder_scopes: REQUIRED_FOR_GENERAL_INTENDED_CALL_RECOVERY",
  "  separator: repeated-indistinguishable-calls",
  "boundary:",
  "  dielectric_model: EVIDENCE_PLAN_REQUIRED",
  "  generic_cse_denotation: NOT_PROVED",
  "  scheduler_checkpoint_codegen: NOT_VERIFIED"]

def renderExecutionError (message : String) : String :=
  String.intercalate "\n" (header ++ [
    "matcher:",
    "  status: REJECTED",
    "  failed_clauses: [\"recording-execution\"]",
    "  execution_error: " ++ reprStr message,
    "cse:",
    "  status: NOT_RUN",
    "authority: none"])

def renderRejected (rawVertices generated : Nat) (obstruction : MatchObstruction) : String :=
  String.intercalate "\n" (header ++ [
    "matcher:",
    "  policy: dependency-closure",
    "  constant_identity: recording-site",
    "  status: REJECTED",
    "  warrant: REJECTED",
    "  generated_candidates: " ++ toString generated,
    "  failed_clauses: " ++ matchClauseList obstruction.failures,
    "  conflicting_vertices: " ++ reprStr obstruction.vertices,
    "  conflicting_occurrences: " ++ reprStr obstruction.occurrences,
    "cse:",
    "  status: NOT_RUN",
    "  raw_vertices: " ++ toString rawVertices,
    "authority: none"])

def renderAmbiguous (rawVertices generated : Nat)
    (classes : List (ConsequenceClass provenance rawGraph))
    (separator : Option AmbiguitySeparator) : String :=
  String.intercalate "\n" (header ++ [
    "matcher:",
    "  policy: dependency-closure",
    "  constant_identity: recording-site",
    "  status: AMBIGUOUS",
    "  warrant: UNKNOWN",
    "  generated_candidates: " ++ toString generated,
    "  consequence_classes: " ++ toString classes.length,
    "  separator: " ++ separatorText separator,
    "cse:",
    "  status: NOT_RUN",
    "  raw_vertices: " ++ toString rawVertices,
    "authority: accepted alternatives only"])

def render : String :=
  match recordRawAndCompact with
  | .error message => renderExecutionError message
  | .ok (raw, _, _, _, _, _, _) =>
      let graph := ofTape raw
      let candidates := generateWorkedModelCandidates graph
      match h : inferWorkedModel graph with
      | .rejected obstruction => renderRejected raw.size candidates.length obstruction
      | .ambiguous classes separator =>
          String.intercalate "\n" (header ++ [
            "matcher:",
            "  policy: dependency-closure",
            "  constant_identity: recording-site",
            "  status: AMBIGUOUS",
            "  warrant: UNKNOWN",
            "  generated_candidates: " ++ toString candidates.length,
            "  consequence_classes: " ++ toString classes.length,
            "  separator: " ++ separatorText separator,
            "cse:",
            "  status: NOT_RUN",
            "  raw_vertices: " ++ toString raw.size,
            "authority: accepted alternatives only"])
      | .inferred resultClass =>
          let sourceMatch := resultClass.representative.sourceMatch
          match certifyCse provenance raw sourceMatch with
          | .rejected rejected =>
              String.intercalate "\n" (header ++ [
                "matcher:",
                "  policy: dependency-closure",
                "  constant_identity: recording-site",
                "  status: INFERRED",
                "  warrant: " ++ warrantText (workedModelWarrant graph),
                "  generated_candidates: " ++ toString candidates.length,
                "  consequence_classes: 1",
                "  equivalent_alternatives: " ++ toString resultClass.alternatives.length,
                "  protected_consequences_equal_control: " ++
                  boolText (sameProtectedConsequences provenance graph sourceMatch rawMatch),
                "  source_match_accepted: true",
                "  failed_clauses: []",
                "cse:",
                "  optimizer: PropertyKindCalculus.Paradigm.TapeCSE.cseCompact",
                "  status: REJECTED",
                "  raw_vertices: " ++ toString raw.size,
                "  compacted_vertices: " ++ toString rejected.compactTape.size,
                "  failed_clauses: " ++ quotientClauseList rejected.failures,
                "authority:",
                "  inferred_acceptance: MatchInferenceCore.AcceptedCandidate.accepted"])
          | .certified certified =>
              String.intercalate "\n" (header ++ [
                "matcher:",
                "  policy: dependency-closure",
                "  constant_identity: recording-site",
                "  status: INFERRED",
                "  warrant: " ++ warrantText (workedModelWarrant graph),
                "  generated_candidates: " ++ toString candidates.length,
                "  consequence_classes: 1",
                "  equivalent_alternatives: " ++ toString resultClass.alternatives.length,
                "  protected_consequences_equal_control: " ++
                  boolText (sameProtectedConsequences provenance graph sourceMatch rawMatch),
                "  source_match_accepted: true",
                "  failed_clauses: []",
                "cse:",
                "  optimizer: PropertyKindCalculus.Paradigm.TapeCSE.cseCompact",
                "  status: CERTIFIED",
                "  raw_vertices: " ++ toString raw.size,
                "  compacted_vertices: " ++ toString certified.compactTape.size,
                "  failed_clauses: []",
                "authority:",
                "  inferred_acceptance: MatchInferenceCore.AcceptedCandidate.accepted",
                "  transported_acceptance: CertifiedCse.accepted",
                "  strong_bisimulation: CertifiedCse.strongBisimulation",
                "  weak_bisimulation: CertifiedCse.weakBisimulation"] ++ semanticBoundary)

end PropertyKindCalculus.Experiments.PkcCertifyRecording

public def main (_args : List String) : IO UInt32 := do
  IO.println PropertyKindCalculus.Experiments.PkcCertifyRecording.render
  pure 0
