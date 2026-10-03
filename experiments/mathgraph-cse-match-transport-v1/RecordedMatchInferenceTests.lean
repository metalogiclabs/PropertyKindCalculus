/-
# RED test: infer the worked-model match from recorder evidence

The implementation must reconstruct the independently authored `rawMatch`; the test imports
the wished-for matcher API before that module exists so the first CI run proves the test is live.
-/

module

public import RecordedMatchInference
public import RecordedCseQualification

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

open PropertyKindCalculus.Experiments.RecordedCseQualification
open PropertyKindCalculus.Experiments.RecordedMatchInference

#guard inferWorkedModelMatch rawGraph == .ok rawMatch

end PropertyKindCalculus.Experiments.RecordedMatchInferenceTests

end Blanket
