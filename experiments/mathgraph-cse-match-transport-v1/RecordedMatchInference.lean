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

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedMatchInference

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)
open PropertyKindCalculus.Experiments.CertifiedCseGate
open PropertyKindCalculus.Experiments.RecordedCseQualification

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

/-- Infer the independently authored source match for the recorded `y = a * b + e` model.
The constant ids are recording-site evidence: the projected tape intentionally carries no
identity for anonymous constant leaves, so numerical equality is never used as identity. -/
def inferWorkedModelMatch (T : TapeGraph) :
    Except (List MatchInferenceFailure) (InferredWorkedModelMatch T) :=
  let a := namedLeaves T ["a.re", "a.im"]
  let b := namedLeaves T ["b.re", "b.im"]
  let e := [7, 16].filter fun v => T.isLeaf v && T.name? v == none
  if a.length != 4 || b.length != 4 || e.length != 2 then
    .error [.sourceEvidence]
  else
    let productFrontier := a ++ b
    let productInterior := readyNamedOps T productFrontier [] ["mul"]
    let c := readyNamedOps T (productFrontier ++ productInterior)
      productInterior ["sub", "add"]
    if productInterior.length != 4 || c.length != 2 then
      .error [.realizationShape]
    else
      let y := readyNamedOps T (c ++ e) (productInterior ++ c) ["add"]
      if y.length != 2 then
        .error [.realizationShape]
      else
        let candidate : Match Nat := {
          components := [(0, a), (1, b), (2, e), (3, c), (4, y)]
          realized := [⟨0, productInterior⟩, ⟨1, []⟩]
        }
        match h : candidate.accepts provenance T with
        | true => .ok ⟨candidate, h⟩
        | false => .error [.acceptance]

/-- The dependency-closure matcher reconstructs the independently authored control match,
field-for-field, on PKC's checked 18-vertex worked tape. -/
theorem inferred_worked_match_eq_control :
    (inferWorkedModelMatch rawGraph).map InferredWorkedModelMatch.sourceMatch = .ok rawMatch := by
  rfl

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
