/-
NFM 2027 coauthor-side source-identity census on the actual AVS residual +
four Jacobian outputs recorded by PKC's existing TapeCodegenEndToEnd.recordRaw.

This is NOT a verifier for scientific-source identity. It measures only which
anonymous constant leaves have equal stored Float bits and which such leaves
the existing cseCompact maps to a common output vertex. When recorder-site
identity is absent, that is a potential provenance ambiguity rather than proof
that two distinct scientific sources were merged.
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

/-- Independent example: one numerical op may legitimately be commoned,
and one leaf merge may violate source identity; classify nothing from bits. -/
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

#eval report

end PropertyKindCalculus.Experiments.AvsTapeAudit

end Blanket
