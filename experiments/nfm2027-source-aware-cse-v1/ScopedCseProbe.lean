/-
Research control: a bounded source-identity distinction for common-subexpression
elimination (CSE) over a recorded tape.

This independent experiment is not a replacement for PKC's upstream optimizer.
It checks whether explicit, externally supplied source identity can preserve two
distinct attested sources with identical floating-point values while still
permitting repeated emissions of one source to share a vertex. Missing source
information causes refusal rather than a guessed assignment.

The general recorder occurrence/scope problem and CPU/GPU equivalence remain open.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
meta import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
public import PropertyKindCalculus.Torch.Paradigm.TapeCse
meta import PropertyKindCalculus.Torch.Paradigm.TapeCse
public import PropertyKindCalculus.Graph.Bisimulation
meta import PropertyKindCalculus.Graph.Bisimulation

@[expose] public section Blanket

open Spec TorchLean
open Runtime.Autograd (Tape TapeM Node)
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (TapeBuilder TapeGraph Match)
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)
open PropertyKindCalculus.Paradigm.TapeCSE (nodeKey cseCompact)

namespace PropertyKindCalculus.Experiments.NfmSourceCse

abbrev TB := TapeBuilder Shape.scalar
abbrev ScopedKey := Option Nat × (Option String × Array Nat × List UInt64)

/-- A source-aware, fail-closed *probe*, not a replacement production pass.
For unnamed constant leaves, attach a declared source identity to the existing
value-oriented key. Every unnamed constant must provide that identity. All other
nodes retain the original key policy. Accepted matches remain a separate gate. -/
def cseScoped (owner : Nat → Option Nat) (t : Tape Float) :
    Except String (Tape Float × Array Nat) := do
  let mut newTape : Tape Float := Tape.empty
  let mut remap : Array Nat := Array.mkEmpty t.size
  let mut memo : Std.HashMap ScopedKey Nat := {}
  -- As the pass processes nodes in original order, remap.size is the original
  -- node index for this iteration. This experiment does not prove a universal
  -- loop invariant or infer owner metadata from the tape.
  for node in t.nodes do
    let sourceClass : Option Nat ←
      if node.parents.isEmpty && node.name == none then
        match owner remap.size with
        | some source => pure (some source)
        | none => throw s!"missing source identity for anonymous leaf {remap.size}"
      else pure none
    let key : ScopedKey := (sourceClass, nodeKey remap node)
    match memo[key]? with
    | some nid =>
        remap := remap.push nid
    | none =>
        let remappedParents := node.parents.map (fun p => remap.getD p p)
        let (newTape', nid) := newTape.addNode { node with parents := remappedParents }
        newTape := newTape'
        memo := memo.insert key nid
        remap := remap.push nid
  pure (newTape, remap)

/-- Different declared source classes make the keys unequal independently of
the floating-point payload. This local key inequality does not prove whole-pass semantic soundness. -/
theorem distinct_sources_distinct_keys (a b : Nat) (h : a ≠ b)
    (r : Array Nat) (x y : Node Float) :
    ((some a, nodeKey r x) : ScopedKey) ≠ ((some b, nodeKey r y) : ScopedKey) := by
  intro heq
  apply h
  exact Option.some.inj (congrArg Prod.fst heq)

/-- Record two anonymous constants using the original PKC tape carrier and
compact through the tested source-aware probe. -/
def recordScoped (aOwner bOwner : Option Nat) (a b : Float) :
    Except String (Tape Float × Nat × Nat × Nat) := do
  let ((x, y), t) ← TapeM.run Tape.empty (do
    let x ← (TapeBuilder.const a : TB).run
    let y ← (TapeBuilder.const b : TB).run
    pure (x, y))
  let owner : Nat → Option Nat := fun i =>
    if i == x then aOwner else if i == y then bOwner else none
  let (t', remap) ← cseScoped owner t
  pure (t', t.size, remap.getD x x, remap.getD y y)

def oneLeaf : TapeGraph := ⟨[⟨none, []⟩]⟩
def twoLeaves : TapeGraph := ⟨[⟨none, []⟩, ⟨none, []⟩]⟩

-- Two emissions belonging to ONE declared source still merge.
#guard (recordScoped (some 0) (some 0) 1.0 1.0).map (fun (t, raw, x, y) =>
  (raw, t.size, x == y, ofTape t == oneLeaf)) == .ok (2, 1, true, true)

-- Two DIFFERENT declared sources with equal Float bits remain distinct.
#guard (recordScoped (some 0) (some 1) 1.0 1.0).map (fun (t, raw, x, y) =>
  (raw, t.size, x == y, ofTape t == twoLeaves)) == .ok (2, 2, false, true)

-- Value-distinct leaves stay distinct regardless of their source identity.
#guard (recordScoped (some 0) (some 0) 1.0 2.0).map (fun (t, raw, x, y) =>
  (raw, t.size, x == y)) == .ok (2, 2, false)

-- Source information absent: reject, never silently merge.
#guard (match recordScoped none (some 1) 1.0 1.0 with
  | .error _ => true
  | .ok _ => false)

/-- The resulting two-vertex graph admits the intended distinct-source match. -/
def twoSources : Provenance Nat Nat where
  ports := []
  intros := [
    ⟨0, 10, .attested "kind 10 source"⟩,
    ⟨1, 20, .attested "kind 20 source"⟩]
  occurrences := []
  exits := []

def twoSourcesMatch : Match Nat where
  components := [(0, [0]), (1, [1])]
  realized := []

#guard twoSources.wellFormed
#guard twoSourcesMatch.accepts twoSources twoLeaves
theorem two_sources_retained_are_acceptable :
    twoSourcesMatch.Accepts twoSources twoLeaves := by decide

-- Exact traceability test: the scoped graph admits the independently specified
-- match, not just two numerically distinct leaf IDs.
#guard (match recordScoped (some 0) (some 1) 1.0 1.0 with
  | .ok (t, _, _, _) => twoSourcesMatch.accepts twoSources (ofTape t)
  | .error _ => false)

/-- info: 'PropertyKindCalculus.Experiments.NfmSourceCse.distinct_sources_distinct_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinct_sources_distinct_keys

end PropertyKindCalculus.Experiments.NfmSourceCse

end Blanket
