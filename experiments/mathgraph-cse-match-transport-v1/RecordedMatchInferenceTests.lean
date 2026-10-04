/- Executable controls for evidence-driven worked-model inference and scope ambiguity. -/

module

public import RecordedMatchInference
public import CertifiedCseControls
public meta import RecordedMatchInference
public meta import CertifiedCseControls

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

open PropertyKindCalculus Provenance
open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Experiments.MatchInferenceCore
open PropertyKindCalculus.Experiments.RecordedCseQualification
open PropertyKindCalculus.Experiments.RecordedMatchInference
open PropertyKindCalculus.Experiments.CertifiedCseGate
open PropertyKindCalculus.Experiments.CertifiedCseControls

#guard (inferWorkedModel rawGraph).status == .inferred
#guard workedModelWarrant rawGraph == .warrantedBounded
#guard match inferWorkedModel rawGraph with
  | .inferred resultClass =>
      sameProtectedConsequences provenance rawGraph
        resultClass.representative.sourceMatch rawMatch
  | _ => false

def undeclaredConstant : TapeGraph :=
  ⟨rawGraph.vertices ++ [⟨none, []⟩]⟩

#guard (inferWorkedModel undeclaredConstant).status == .rejected
#guard match inferWorkedModel undeclaredConstant with
  | .rejected obstruction =>
      obstruction.failures.contains .leavesAreSources && obstruction.vertices == [18]
  | _ => false

def missingConstantSite : TapeGraph :=
  ⟨rawGraph.vertices.take 16 ++ [⟨some "untracked.e", []⟩] ++
    rawGraph.vertices.drop 17⟩

#guard match inferWorkedModel missingConstantSite with
  | .rejected obstruction => obstruction.failures == [.noCandidates]
  | _ => false

/-- Vertex 2 is offered to both occurrences. -/
def overlappingInteriors : Match Nat where
  components := rawMatch.components
  realized := [⟨0, [2, 5, 11, 14]⟩, ⟨1, [2]⟩]

#guard (classifyCandidates provenance rawGraph [overlappingInteriors]).status == .rejected
#guard match classifyCandidates provenance rawGraph [overlappingInteriors] with
  | .rejected obstruction =>
      obstruction.failures.contains .realizedTopology &&
      obstruction.failures.contains .interiorsDisjoint
  | _ => false

/- Equal-valued distinct sources survive matching but the actual CSE quotient is rejected. -/
#guard distinctSourceRawMatch.accepts distinctSourceProvenance ⟨[⟨none, []⟩, ⟨none, []⟩]⟩
#guard distinctSourceCertification.map CseCertification.isCertified == .ok false
#guard distinctSourceCertification.map CseCertification.failedClauses ==
  .ok [.componentOwnership, .componentMultiplicity]

/- Two identical member calls with no tape-visible scope distinction. -/
def repeatedCallProvenance : Provenance Nat Nat where
  ports := [⟨0, 0, .input⟩]
  intros := [⟨1, 0, .derived⟩, ⟨2, 0, .derived⟩]
  occurrences := [
    ⟨.additive, [(0, 0)], 1, 0, "call-1", .anonymous⟩,
    ⟨.additive, [(0, 0)], 2, 0, "call-2", .anonymous⟩]
  exits := []

def repeatedCallTape : TapeGraph := ⟨[
  ⟨some "x", []⟩,
  ⟨some "member", [0]⟩, ⟨some "result", [1]⟩,
  ⟨some "member", [0]⟩, ⟨some "result", [3]⟩]⟩

def scopedCalls : Match Nat where
  components := [(0, [0]), (1, [2]), (2, [4])]
  realized := [⟨0, [1]⟩, ⟨1, [3]⟩]

def crossedCalls : Match Nat where
  components := [(0, [0]), (1, [4]), (2, [2])]
  realized := [⟨0, [3]⟩, ⟨1, [1]⟩]

#guard scopedCalls.accepts repeatedCallProvenance repeatedCallTape
#guard crossedCalls.accepts repeatedCallProvenance repeatedCallTape
#guard match classifyCandidates repeatedCallProvenance repeatedCallTape
    [scopedCalls, crossedCalls] with
  | .ambiguous _ (some separator) => separator.kind == .componentOwnership
  | _ => false

def reorderedRawMatch : Match Nat where
  components := rawMatch.components.reverse
  realized := rawMatch.realized.reverse

#guard match classifyCandidates provenance rawGraph [rawMatch, reorderedRawMatch] with
  | .inferred resultClass => resultClass.alternatives.length == 1
  | _ => false

end PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

end Blanket
