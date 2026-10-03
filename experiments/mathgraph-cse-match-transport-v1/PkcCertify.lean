/- Command-line, replayable manifest for the MathGraph PKC CSE certification gate. -/

module

public import CertifiedCseControls
public meta import CertifiedCseControls

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm
open Runtime.Autograd (Tape)

namespace PropertyKindCalculus.Experiments.PkcCertify

open CertifiedCseGate
open CertifiedCseControls
open CseQuotientChecker

def boolText (b : Bool) : String := if b then "true" else "false"

def clauseList (cs : List TapeQuotientClause) : String :=
  "[" ++ String.intercalate ", " (cs.map fun c => "\"" ++ c.label ++ "\"") ++ "]"

def auditManifest (a : TapeQuotientAudit) : String :=
  String.intercalate "\n" [
    "  component_ownership: " ++ boolText a.identity.components,
    "  interior_ownership: " ++ boolText a.identity.interiors,
    "  role_separation: " ++ boolText a.identity.roles,
    "  target_ordered: " ++ boolText a.ordered,
    "  target_total: " ++ boolText a.total,
    "  component_multiplicity: " ++ boolText a.componentMultiplicity,
    "  leaves_are_sources: " ++ boolText a.leafSources,
    "  sources_are_leaves: " ++ boolText a.sourceLeaves,
    "  realized_topology: " ++ boolText a.realizedTopology,
    "  interior_multiplicity: " ++ boolText a.interiorMultiplicity,
    "  coverage: " ++ boolText a.coverage]

def header (scenario : String) : List String := [
  "mathgraph_pkc_certification: 1",
  "pkc_revision: 6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9",
  "scenario: " ++ scenario,
  "optimizer: PropertyKindCalculus.Paradigm.TapeCSE.cseCompact",
  "match_source: supplied"]

def renderCertification [BEq ν] [BEq κ] (scenario : String) (g : Provenance ν κ)
    (m : Match ν) (rawSize : Nat) (result : CseCertification g m) : String :=
  match result with
  | .certified c =>
      let audit := auditTapeQuotient g c.targetGraph m c.vertexMap
      String.intercalate "\n" (header scenario ++ [
        "status: CERTIFIED",
        "source_match_accepted: true",
        "raw_vertices: " ++ toString rawSize,
        "compacted_vertices: " ++ toString c.compactTape.size,
        "remap: " ++ reprStr c.remap.toList,
        "failed_clauses: []",
        "audit:",
        auditManifest audit,
        "authority:",
        "  source_acceptance: CertifiedCse.sourceAccepted",
        "  source_acceptance_axioms: [propext, Classical.choice, Quot.sound]",
        "  acceptance: CertifiedCse.accepted",
        "  acceptance_axioms: [propext, Classical.choice, Quot.sound]",
        "  strong_bisimulation: CertifiedCse.strongBisimulation",
        "  strong_bisimulation_axioms: [propext, Classical.choice, Quot.sound]",
        "  weak_bisimulation: CertifiedCse.weakBisimulation",
        "  weak_bisimulation_axioms: [propext, Classical.choice, Quot.sound]",
        "boundary: the gate checks a supplied match; this is not automatic matching or universal optimizer correctness"])
  | .rejected r =>
      String.intercalate "\n" (header scenario ++ [
        "status: REJECTED",
        "source_match_accepted: " ++ boolText r.sourceAccepted,
        "raw_vertices: " ++ toString rawSize,
        "compacted_vertices: " ++ toString r.compactTape.size,
        "remap: " ++ reprStr r.remap.toList,
        "failed_clauses: " ++ clauseList r.failures,
        "audit:",
        auditManifest r.audit,
        "authority: none (quotient not admitted)",
        "boundary: rejection is a certified residual of the supplied provenance correspondence"])

def renderError (scenario e : String) : String :=
  String.intercalate "\n" (header scenario ++ [
    "status: EXECUTION_ERROR",
    "error: " ++ reprStr e,
    "authority: none"])

def renderWorkedModel : String :=
  match RecordedCseQualification.recordRawAndCompact with
  | .error e => renderError "worked-model" e
  | .ok (raw, _, _, _, _, _, _) =>
      renderCertification "worked-model" RecordedCseQualification.provenance
        RecordedCseQualification.rawMatch raw.size
        (certifyCse RecordedCseQualification.provenance raw RecordedCseQualification.rawMatch)

def renderDistinctSourceMutant : String :=
  match recordEqualConstants with
  | .error e => renderError "distinct-source-mutant" e
  | .ok raw =>
      renderCertification "distinct-source-mutant" distinctSourceProvenance
        distinctSourceRawMatch raw.size
        (certifyCse distinctSourceProvenance raw distinctSourceRawMatch)

def renderUndeclaredConstantMutant : String :=
  match recordWorkedWithUndeclaredConstant with
  | .error e => renderError "undeclared-constant-mutant" e
  | .ok raw =>
      renderCertification "undeclared-constant-mutant" RecordedCseQualification.provenance
        RecordedCseQualification.rawMatch raw.size
        (certifyCse RecordedCseQualification.provenance raw RecordedCseQualification.rawMatch)

def renderScenario : String → Option String
  | "worked-model" => some renderWorkedModel
  | "distinct-source-mutant" => some renderDistinctSourceMutant
  | "undeclared-constant-mutant" => some renderUndeclaredConstantMutant
  | "all" => some (String.intercalate "\n---\n"
      [renderWorkedModel, renderDistinctSourceMutant, renderUndeclaredConstantMutant])
  | _ => none

def run (args : List String) : IO UInt32 := do
  let scenario := args.head?.getD "worked-model"
  match renderScenario scenario with
  | some manifest =>
      IO.println manifest
      pure 0
  | none =>
      IO.eprintln "usage: pkc-certify [worked-model|distinct-source-mutant|undeclared-constant-mutant|all]"
      pure 2

end PropertyKindCalculus.Experiments.PkcCertify

public def main (args : List String) : IO UInt32 :=
  PropertyKindCalculus.Experiments.PkcCertify.run args
