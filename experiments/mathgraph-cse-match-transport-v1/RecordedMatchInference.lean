/-
# Automatic match inference for PKC's recorded complex worked model

This is the minimum dependency-closure experiment requested by PKC's capstone ledger.  It
reconstructs the source match from evidence visible at the recorder boundary:

* named port emissions (`a.re`, `a.im`, `b.re`, `b.im`);
* the two recording sites of the attested complex constant;
* the complex-product realization shape (four `mul` interiors, `sub`/`add` roots); and
* the complex-additive realization shape (two `add` roots).

It deliberately remains a worked-model instrument.  A generic matcher still needs harvested
port/recording-site metadata and a realization table indexed by family and carrier.
-/

module

public import CertifiedCseGate
public import MatchInferenceCore

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedMatchInference

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)
open PropertyKindCalculus.Experiments.CertifiedCseGate
open PropertyKindCalculus.Experiments.MatchInferenceCore
open PropertyKindCalculus.Experiments.RecordedCseQualification

/-! ## Explicit recorder evidence -/

/-- Names and expected emission count for one named source node. -/
structure NamedSourceEvidence where
  node : Nat
  names : List String
  expectedComponents : Nat
deriving DecidableEq, Repr, BEq

/-- Recorder-site identities for a source whose projected tape vertices are anonymous. -/
structure SiteSourceEvidence where
  node : Nat
  recordingSites : List Nat
deriving DecidableEq, Repr, BEq

/-- The finite realization vocabulary used to recognize one provenance occurrence. -/
structure OccurrenceEvidence where
  occurrence : Nat
  family : Provenance.EdgeFamily
  carrier : String
  interiorNames : List String
  rootNames : List String
  expectedInterior : Nat
  expectedRoots : Nat
deriving DecidableEq, Repr, BEq

/-- Evidence that survives the recorder boundary for the checked complex worked model. -/
structure WorkedModelEvidence where
  namedSources : List NamedSourceEvidence
  siteSources : List SiteSourceEvidence
  occurrences : List OccurrenceEvidence
deriving DecidableEq, Repr, BEq

def workedModelEvidence : WorkedModelEvidence where
  namedSources := [
    ⟨0, ["a.re", "a.im"], 4⟩,
    ⟨1, ["b.re", "b.im"], 4⟩]
  siteSources := [⟨2, [7, 16]⟩]
  occurrences := [
    ⟨0, .product, "Float", ["mul"], ["sub", "add"], 4, 2⟩,
    ⟨1, .additive, "Float", [], ["add"], 0, 2⟩]

def WorkedModelEvidence.namedSource? (e : WorkedModelEvidence) (node : Nat) :
    Option NamedSourceEvidence :=
  e.namedSources.find? fun source => source.node == node

def WorkedModelEvidence.siteSource? (e : WorkedModelEvidence) (node : Nat) :
    Option SiteSourceEvidence :=
  e.siteSources.find? fun source => source.node == node

def WorkedModelEvidence.occurrence? (e : WorkedModelEvidence) (occurrence : Nat) :
    Option OccurrenceEvidence :=
  e.occurrences.find? fun shape => shape.occurrence == occurrence

/-- Stable residual classes for the first automatic matcher boundary. -/
inductive MatchInferenceFailure where
  | sourceEvidence
  | realizationShape
  | acceptance
deriving DecidableEq, Repr, BEq

def MatchInferenceFailure.label : MatchInferenceFailure → String
  | .sourceEvidence => "source-evidence"
  | .realizationShape => "realization-shape"
  | .acceptance => "match-acceptance"

/-- Successful inference retains the kernel-checkable admission fact consumed by PKC's
bisimulation theorems.  The matcher does not merely return an unchecked table. -/
structure InferredWorkedModelMatch (T : TapeGraph) where
  sourceMatch : Match Nat
  accepted : sourceMatch.Accepts provenance T

/-- All leaf emissions carrying one of the recorder names, in tape order. -/
def namedLeaves (T : TapeGraph) (names : List String) : List Nat :=
  (List.range T.size).filter fun v =>
    T.isLeaf v && names.contains ((T.name? v).getD "")

/-- Operation vertices of one realization stage whose dependencies are already available.
This is the dependency-closure policy: a candidate belongs to the occurrence only when every
parent is in its current frontier or in an earlier stage of the same realization. -/
def readyNamedOps (T : TapeGraph) (available claimed : List Nat)
    (names : List String) : List Nat :=
  (List.range T.size).filter fun v =>
    T.isOp v && !claimed.contains v &&
      names.contains ((T.name? v).getD "") &&
      (T.parents v).all available.contains

/-- Anonymous leaves selected by recorder identity, never by their numerical values. -/
def siteLeaves (T : TapeGraph) (sites : List Nat) : List Nat :=
  sites.filter fun v => v < T.size && T.isLeaf v && T.name? v == none

/-- Generate the finite candidate set from recorder evidence and dependency closure.  An
extra tape leaf intentionally does not suppress candidate construction: `Match.accepts` must
name that undeclared dependency in its residual instead of the generator hiding it. -/
def generateWorkedModelCandidates (T : TapeGraph) : List (Match Nat) :=
  match workedModelEvidence.namedSource? 0, workedModelEvidence.namedSource? 1,
      workedModelEvidence.siteSource? 2, workedModelEvidence.occurrence? 0,
      workedModelEvidence.occurrence? 1 with
  | some aEvidence, some bEvidence, some eEvidence, some product, some addition =>
      if product.family != .product || product.carrier != "Float" ||
          addition.family != .additive || addition.carrier != "Float" then []
      else
        let a := namedLeaves T aEvidence.names
        let b := namedLeaves T bEvidence.names
        let e := siteLeaves T eEvidence.recordingSites
        if a.length != aEvidence.expectedComponents ||
            b.length != bEvidence.expectedComponents ||
            e.length != eEvidence.recordingSites.length then []
        else
          let productFrontier := a ++ b
          let productInterior := readyNamedOps T productFrontier [] product.interiorNames
          let c := readyNamedOps T (productFrontier ++ productInterior)
            productInterior product.rootNames
          if productInterior.length != product.expectedInterior ||
              c.length != product.expectedRoots then []
          else
            let y := readyNamedOps T (c ++ e) (productInterior ++ c) addition.rootNames
            if addition.expectedInterior != 0 || y.length != addition.expectedRoots then []
            else [{
              components := [(0, a), (1, b), (2, e), (3, c), (4, y)]
              realized := [⟨product.occurrence, productInterior⟩,
                ⟨addition.occurrence, []⟩]
            }]
  | _, _, _, _, _ => []

/-- Infer one accepted consequence class, expose protected ambiguity, or retain the exact
acceptance obstruction. -/
def inferWorkedModel (T : TapeGraph) : MatchInferenceOutcome provenance T :=
  classifyCandidates provenance T (generateWorkedModelCandidates T)

/-- Strength of the policy conclusion, separate from the match outcome itself. -/
inductive WarrantStatus where
  | warrantedBounded
  | unknown
  | rejected
deriving DecidableEq, Repr, BEq

/-- Dependency closure is warranted only for the checked 18-vertex worked model. -/
def workedModelWarrant (T : TapeGraph) : WarrantStatus :=
  match inferWorkedModel T with
  | .inferred resultClass =>
      if T == rawGraph && sameProtectedConsequences provenance T
          resultClass.representative.sourceMatch rawMatch then
        .warrantedBounded
      else .unknown
  | .ambiguous _ _ => .unknown
  | .rejected _ => .rejected

/-- Infer the independently authored source match for the recorded `y = a * b + e` model.
The constant ids are recording-site evidence: the projected tape intentionally carries no
identity for anonymous constant leaves, so numerical equality is never used as identity. -/
def inferWorkedModelMatch (T : TapeGraph) :
    Except (List MatchInferenceFailure) (InferredWorkedModelMatch T) :=
  match inferWorkedModel T with
  | .inferred resultClass =>
      .ok ⟨resultClass.representative.sourceMatch,
        resultClass.representative.accepted⟩
  | .ambiguous _ _ => .error [.acceptance]
  | .rejected obstruction =>
      if obstruction.failures.contains .noCandidates then
        .error [.sourceEvidence]
      else .error [.acceptance]

/-- The inferred result preserves the independently authored control's protected
consequences; literal table identity is intentionally not part of the contract. -/
theorem inferred_worked_match_equivalent_control :
    match inferWorkedModel rawGraph with
    | .inferred resultClass =>
        sameProtectedConsequences provenance rawGraph
          resultClass.representative.sourceMatch rawMatch
    | _ => false := by
  decide

/-- Stable, non-dependent outcome for the complete recorded-to-certified executable path. -/
inductive AutomaticCertificationOutcome where
  | inferenceRejected (failures : List MatchInferenceFailure)
  | optimizationRejected (failures : List TapeQuotientClause)
  | certified
deriving DecidableEq, Repr, BEq

/-- Record the actual worked computation, infer an accepted match from its graph, run the actual
CSE pass, and accept the optimized graph only through the existing proof-carrying gate. -/
def certifyInferredWorkedRecording : Except String AutomaticCertificationOutcome :=
  recordRawAndCompact.map fun (raw, _, _, _, _, _, _) =>
    match inferWorkedModelMatch (ofTape raw) with
    | .error failures => .inferenceRejected failures
    | .ok inferred =>
        match certifyCse provenance raw inferred.sourceMatch with
        | .certified _ => .certified
        | .rejected rejected => .optimizationRejected rejected.failures

end PropertyKindCalculus.Experiments.RecordedMatchInference

end Blanket
