/-
# Worked-model match inference controls

The implementation must reconstruct the independently authored `rawMatch`, preserve acceptance
authority, and reject mutations at the precise evidence boundary they violate.
-/

module

public import RecordedMatchInference
public import RecordedCseQualification
public meta import RecordedMatchInference

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Experiments.RecordedCseQualification
open PropertyKindCalculus.Experiments.RecordedMatchInference

#guard match inferWorkedModelMatch rawGraph with
  | .ok inferred => inferred.sourceMatch == rawMatch
  | .error _ => false

/- Extra named emission makes the source assignment ambiguous. -/
def ambiguousNamedSource : TapeGraph :=
  ⟨rawGraph.vertices ++ [⟨some "a.re", []⟩]⟩

/- An otherwise unclaimed anonymous leaf must be rejected by final Match.accepts admission. -/
def undeclaredConstant : TapeGraph :=
  ⟨rawGraph.vertices ++ [⟨none, []⟩]⟩

/- Removing one pinned recording site destroys the constant-source evidence. -/
def missingConstantSite : TapeGraph :=
  ⟨rawGraph.vertices.take 16 ++ [⟨some "untracked.e", []⟩] ++
    rawGraph.vertices.drop 17⟩

/- Renaming one partial product destroys the declared complex-product realization shape. -/
def malformedProductRealization : TapeGraph :=
  ⟨rawGraph.vertices.take 14 ++ [⟨some "not-mul", [12, 13]⟩] ++
    rawGraph.vertices.drop 15⟩

#guard match inferWorkedModelMatch ambiguousNamedSource with
  | .error [.sourceEvidence] => true
  | _ => false

#guard match inferWorkedModelMatch missingConstantSite with
  | .error [.sourceEvidence] => true
  | _ => false

#guard match inferWorkedModelMatch malformedProductRealization with
  | .error [.realizationShape] => true
  | _ => false

#guard match inferWorkedModelMatch undeclaredConstant with
  | .error [.acceptance] => true
  | _ => false

#guard match certifyInferredWorkedRecording with
  | .ok .certified => true
  | _ => false

end PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

end Blanket
