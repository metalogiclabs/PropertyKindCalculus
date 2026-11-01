/- Deliberate negative consumer: must fail at a native type mismatch. -/
module
public import NativeInterventions
@[expose] public section

open PropertyKindCalculus PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Experiments.CertifiedCseGate
open PropertyKindCalculus.Experiments.NativeInterventions
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)

example {ν κ : Type} [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) :=
  weakenedConclusion c
