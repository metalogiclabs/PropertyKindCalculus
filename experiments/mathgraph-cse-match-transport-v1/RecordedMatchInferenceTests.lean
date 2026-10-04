/-
# Worked-model match inference tests

The matcher must reconstruct the independently authored `rawMatch` from recorder evidence.
-/

module

public import RecordedMatchInference
public import RecordedCseQualification

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

open PropertyKindCalculus.Experiments.RecordedCseQualification
open PropertyKindCalculus.Experiments.RecordedMatchInference

#guard match inferWorkedModelMatch rawGraph with
  | .ok inferred => inferred == rawMatch
  | .error _ => false

end PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

end Blanket
