/-
Reproducible numeric-sharing census on PKC's recorded AVS residual and four
Jacobian outputs (TapeCodegenEndToEnd.recordRaw).

This is a measurement of bit-equal anonymous constant leaves and their images
under the existing cseCompact pass, not an audit of scientific-source identity.
The tape does not encode whether a repeated numeric literal is an independently
attested source or a shared structural constant. The result therefore cannot
classify any numerical merge as a scientific-provenance violation.
-/

module

public import PropertyKindCalculus.Examples.TapeCodegenEndToEnd
meta import PropertyKindCalculus.Examples.TapeCodegenEndToEnd
public import PropertyKindCalculus.Torch.Paradigm.TapeCse
meta import PropertyKindCalculus.Torch.Paradigm.TapeCse

@[expose] public section Blanket

open Spec TorchLean
open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Examples.TapeCodegenEndToEnd (recordRaw)

namespace PropertyKindCalculus.Experiments.AvsTapeAudit

abbrev Bits := List UInt64

/-- Numerically anonymous leaf payloads; there is NO source-identity label here. -/
def anonymousLeaves (t : Tape Float) : List (Nat × Bits) :=
  (List.range t.size).filterMap fun i =>
    match t.getNode? i with
    | none => none
    | some n =>
      if n.parents.isEmpty && n.name == none then
        some (i, (TorchLean.Storage.toArray n.value.tensor.buffer).toList.map Float.toBits)
      else none

def equalValuePairs (t : Tape Float) : List (Nat × Nat × Bits) :=
  let leaves := anonymousLeaves t
  leaves.flatMap fun (i, bi) =>
    leaves.filterMap fun (j, bj) =>
      if i < j && bi == bj then some (i, j, bi) else none

/-- Pairs numerically merged by the upstream CSE pass (not yet classified
as legal/illegal provenance merges because source sites are missing). -/
def mergedAnonymousPairs (t : Tape Float) : List (Nat × Nat × Bits) :=
  let remap := (cseCompact t).2
  (equalValuePairs t).filter fun (i, j, _) =>
    remap.getD i i == remap.getD j j

/-- Report numerical sharing without assigning any source-equivalence meaning. -/
def report : IO Unit := do
  match recordRaw with
  | .error e => throw (IO.userError s!"AVS recording failed: {e}")
  | .ok (t, outputs) =>
    let (tc, _) := cseCompact t
    let a := anonymousLeaves t
    let e := equalValuePairs t
    let m := mergedAnonymousPairs t
    IO.println "NFM_AVS_RECORDING_CENSUS_V1"
    IO.println s!"raw_nodes: {t.size}"
    IO.println s!"compacted_nodes: {tc.size}"
    IO.println s!"outputs: {outputs.length}"
    IO.println s!"anonymous_constant_leaves: {a.length}"
    IO.println s!"equal_value_anonymous_pairs: {e.length}"
    IO.println s!"equal_value_pairs_merged_by_cse: {m.length}"
    IO.println s!"first_merged_pair: {repr (m.head?)}"
    IO.println "source_identity_status: UNKNOWN_NOT_RECORDED"
    IO.println "scientific_provenance_violation: NOT_INFERRED_FROM_VALUE_BITS"

/-- Freeze the observed census of the pinned AVS recording. A change in
the recording or CSE implementation must explicitly requalify these counts;
passing this check does not establish provenance or GPU correctness. -/
def expectedCensus : Bool :=
  match recordRaw with
  | .error _ => false
  | .ok (t, outputs) =>
      let (tc, _) := cseCompact t
      t.size == 54 &&
      tc.size == 28 &&
      outputs.length == 5 &&
      (anonymousLeaves t).length == 11 &&
      (equalValuePairs t).length == 21 &&
      (mergedAnonymousPairs t).length == 21

#guard expectedCensus
#eval report

end PropertyKindCalculus.Experiments.AvsTapeAudit

end Blanket
