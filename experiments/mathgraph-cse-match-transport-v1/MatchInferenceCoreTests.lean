/- Executable controls for consequence-quotiented match classification. -/

module

public import MatchInferenceCore
public import RecordedCseQualification
public meta import MatchInferenceCore
public meta import RecordedCseQualification

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.MatchInferenceCoreTests

open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Experiments.MatchInferenceCore
open PropertyKindCalculus.Experiments.RecordedCseQualification

/-- Same correspondence, different authored table order. -/
def reorderedRawMatch : Match Nat where
  components := rawMatch.components.reverse
  realized := rawMatch.realized.reverse

/-- Still accepted structurally, but changes the provenance owner of every `a`/`b` component. -/
def swappedSourceOwners : Match Nat where
  components := [
    (0, [1, 4, 10, 13]), (1, [0, 3, 9, 12]), (2, [7, 16]),
    (3, [6, 15]), (4, [8, 17])]
  realized := [⟨0, [2, 5, 11, 14]⟩, ⟨1, []⟩]

#guard rawMatch.accepts provenance rawGraph
#guard reorderedRawMatch.accepts provenance rawGraph
#guard swappedSourceOwners.accepts provenance rawGraph

#guard sameProtectedConsequences provenance rawGraph rawMatch reorderedRawMatch
#guard !sameProtectedConsequences provenance rawGraph rawMatch swappedSourceOwners

#guard (classifyCandidates provenance rawGraph [rawMatch, reorderedRawMatch]).status == .inferred
#guard (classifyCandidates provenance rawGraph [rawMatch, swappedSourceOwners]).status == .ambiguous
#guard (classifyCandidates provenance rawGraph []).status == .rejected

#guard match classifyCandidates provenance rawGraph [rawMatch, swappedSourceOwners] with
  | .ambiguous _ separator => separator != none
  | _ => false

#guard smallestSeparator [
    ⟨.operationOwnership, 0⟩,
    ⟨.componentOwnership, 7⟩,
    ⟨.componentOwnership, 2⟩,
    ⟨.occurrenceBoundary, 0⟩] == some ⟨.componentOwnership, 2⟩

#guard match classifyCandidates provenance rawGraph [] with
  | .rejected obstruction => !obstruction.failures.isEmpty
  | _ => false

end PropertyKindCalculus.Experiments.MatchInferenceCoreTests

end Blanket
