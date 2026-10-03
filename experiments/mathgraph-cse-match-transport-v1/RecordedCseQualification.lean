/-
# MathGraph qualification: PKC's recorded worked model through executable CSE

This module connects the actual tape recorder and `cseCompact` remap for `y = a * b + e`
to the executable quotient audit and PKC's accepted-match bisimulation capstones.
-/

module


public import CseQuotientChecker
public import PropertyKindCalculus.Tests.Torch.TapeSeal
public meta import CseQuotientChecker
public meta import PropertyKindCalculus.Tests.Torch.TapeSeal

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.RecordedCseQualification

open Spec TorchLean
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (TapeGraph Match Realized)
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Tests.TapeSeal (y)
open PropertyKindCalculus.Experiments.CseMatchTransport (transportMatch)
open PropertyKindCalculus.Experiments.CseQuotientChecker

abbrev TB := PropertyKindCalculus.Tests.TapeSeal.TB

/-- Record the worked expression once, retaining both the raw tape and the actual CSE result. -/
def recordRawAndCompact :
    Except String (Tape Float × Tape Float × Array Nat × Nat × Nat × Nat × Nat) := do
  let ((r, i), raw) ← TapeM.run Tape.empty (do
    let r ← y.re.run
    let i ← y.im.run
    pure (r, i))
  let (compact, remap) := cseCompact raw
  pure (raw, compact, remap, r, i, remap.getD r r, remap.getD i i)

/-- The measured raw graph, before CSE shares the repeated input emissions. -/
def rawGraph : TapeGraph := ⟨[
  ⟨some "a.re", []⟩, ⟨some "b.re", []⟩, ⟨some "mul", [0, 1]⟩,
  ⟨some "a.im", []⟩, ⟨some "b.im", []⟩, ⟨some "mul", [3, 4]⟩,
  ⟨some "sub", [2, 5]⟩, ⟨none, []⟩, ⟨some "add", [6, 7]⟩,
  ⟨some "a.re", []⟩, ⟨some "b.im", []⟩, ⟨some "mul", [9, 10]⟩,
  ⟨some "a.im", []⟩, ⟨some "b.re", []⟩, ⟨some "mul", [12, 13]⟩,
  ⟨some "add", [11, 14]⟩, ⟨none, []⟩, ⟨some "add", [15, 16]⟩]⟩

/-- The actual old-to-new remap returned by `cseCompact` for the recorded worked model. -/
def actualRemap : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6
  | 7 => 7 | 8 => 8 | 9 => 0 | 10 => 4 | 11 => 9 | 12 => 3 | 13 => 1
  | 14 => 10 | 15 => 11 | 16 => 12 | 17 => 13
  | n => n

/-- The accepted match before CSE. Repeated source components record repeated emissions of
the same named inputs; the two realization interiors remain disjoint. -/
def rawMatch : Match Nat where
  components := [
    (0, [0, 3, 9, 12]), (1, [1, 4, 10, 13]), (2, [7, 16]),
    (3, [6, 15]), (4, [8, 17])]
  realized := [⟨0, [2, 5, 11, 14]⟩, ⟨1, []⟩]

abbrev provenance := PropertyKindCalculus.Tests.Bisimulation.g
abbrev compactGraph := PropertyKindCalculus.Tests.TapeSeal.T
abbrev compactMatch := PropertyKindCalculus.Tests.TapeSeal.m

/-! ## The executable recorder/CSE boundary -/

#guard (recordRawAndCompact.map fun (raw, _, _, _, _, _, _) => ofTape raw == rawGraph) == .ok true
#guard (recordRawAndCompact.map fun (_, compact, _, _, _, _, _) =>
  ofTape compact == compactGraph) == .ok true
#guard (recordRawAndCompact.map fun (_, _, remap, r, i, r', i') =>
  (remap.toList, r, i, r', i')) ==
    .ok ([0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 4, 9, 3, 1, 10, 11, 12, 13],
      8, 17, 8, 13)

#guard rawMatch.accepts provenance rawGraph

lemma raw_accepted : rawMatch.Accepts provenance rawGraph := by decide

/- Mapping preserves repeated emissions as duplicate entries.  Erasing only duplicate vertex
ids yields exactly the independently authored compacted control match already in PKC. -/
def canonicalizeMatch (m : Match ν) : Match ν where
  components := m.components.map fun e => (e.1, e.2.eraseDups)
  realized := m.realized.map fun r => { r with interior := r.interior.eraseDups }

#guard canonicalizeMatch (transportMatch actualRemap rawMatch) == compactMatch
#guard (auditTapeQuotient provenance compactGraph rawMatch actualRemap).passed

theorem recorded_audit_passes :
    (auditTapeQuotient provenance compactGraph rawMatch actualRemap).passed = true := by decide

theorem recorded_cse_accepts :
    (transportMatch actualRemap rawMatch).Accepts provenance compactGraph :=
  acceptance_of_audit raw_accepted recorded_audit_passes

lemma provenance_wellFormed : provenance.WellFormed := by decide

theorem recorded_cse_strong_bisimulation :
    Cslib.LTS.IsBisimulation provenance.lts
      ((transportMatch actualRemap rawMatch).contracted provenance)
      (Match.obs (transportMatch actualRemap rawMatch)) :=
  strong_bisimulation_of_audit provenance_wellFormed raw_accepted recorded_audit_passes

theorem recorded_cse_weak_bisimulation :
    Cslib.LTS.IsWeakBisimulation provenance.lts
      ((transportMatch actualRemap rawMatch).tapeLts provenance compactGraph)
      (Match.weak provenance (transportMatch actualRemap rawMatch)) :=
  weak_bisimulation_of_audit provenance_wellFormed raw_accepted recorded_audit_passes

/-! ## Pinned axiom profiles -/

/-- info: 'PropertyKindCalculus.Experiments.RecordedCseQualification.recorded_audit_passes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_audit_passes

/-- info: 'PropertyKindCalculus.Experiments.RecordedCseQualification.recorded_cse_accepts' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_cse_accepts

/-- info: 'PropertyKindCalculus.Experiments.RecordedCseQualification.recorded_cse_strong_bisimulation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_cse_strong_bisimulation

/-- info: 'PropertyKindCalculus.Experiments.RecordedCseQualification.recorded_cse_weak_bisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_cse_weak_bisimulation

end PropertyKindCalculus.Experiments.RecordedCseQualification

end Blanket
