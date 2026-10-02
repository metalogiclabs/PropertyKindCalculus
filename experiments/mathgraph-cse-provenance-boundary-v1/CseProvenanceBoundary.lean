/-
# MathGraph qualification probe: executable CSE versus metrological identity

This file is deliberately external to PKC's declared libraries.  It is a bounded,
independently buildable probe of the missing bridge between the executable `cseCompact`
pass and `Match.accepts`, not a proposed change to either definition.

The separator is minimal: two anonymous constants with identical Float bits are one node
after CSE.  That is lawful when they are two emissions of one metrological source.  It is
not representable by an accepted match when the two occurrences stand for two distinct
declared sources, because accepted component assignments are total and injective.
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
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (TapeBuilder TapeGraph Match)
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)

namespace PropertyKindCalculus.Experiments.CseProvenanceBoundary

abbrev TB := TapeBuilder Shape.scalar

/-- Record two anonymous constants, compact the tape, and retain both old-to-new images. -/
def recordConstants (a b : Float) : Except String (Tape Float × Nat × Nat × Nat) := do
  let ((x, y), t) ← TapeM.run Tape.empty (do
    let x ← (TapeBuilder.const a : TB).run
    let y ← (TapeBuilder.const b : TB).run
    pure (x, y))
  let (t', remap) := cseCompact t
  pure (t', t.size, remap.getD x x, remap.getD y y)

/-! ## Executable controls for the current CSE key -/

-- Distinct value bits remain distinct.
#guard (recordConstants 1.0 2.0).map (fun (t, raw, x, y) =>
  (raw, t.size, x == y)) == .ok (2, 2, false)

-- Equal anonymous constants are merged and both old ids map to the same new id.
#guard (recordConstants 1.0 1.0).map (fun (t, raw, x, y) =>
  (raw, t.size, x == y)) == .ok (2, 1, true)

/-- One anonymous constant leaf: the graph produced by the equal-value control. -/
def oneLeaf : TapeGraph := ⟨[⟨none, []⟩]⟩

#guard (recordConstants 1.0 1.0).map (fun (t, _, _, _) => ofTape t == oneLeaf) == .ok true

/-! ## NULL/control: repeated emission of one metrological source is admissible -/

/-- One declared attested source. -/
def oneSource : Provenance Nat Nat where
  ports := []
  intros := [⟨0, 10, .attested "one source"⟩]
  occurrences := []
  exits := []

/-- Both runtime emissions may be treated as one source after CSE. -/
def oneSourceMatch : Match Nat where
  components := [(0, [0])]
  realized := []

#guard oneSource.wellFormed
#guard oneSourceMatch.accepts oneSource oneLeaf

lemma one_source_accepted : oneSourceMatch.Accepts oneSource oneLeaf := by decide

/-! ## Separator: equal raw values do not imply equal metrological sources -/

/-- Two declared attested sources with different kinds happen to carry the same raw number. -/
def twoKinds : Provenance Nat Nat where
  ports := []
  intros := [
    ⟨0, 10, .attested "kind 10 source"⟩,
    ⟨1, 20, .attested "kind 20 source"⟩]
  occurrences := []
  exits := []

/-- With only vertex 0 left, the evident table makes both source nodes claim it. -/
def collapsedKindsMatch : Match Nat where
  components := [(0, [0]), (1, [0])]
  realized := []

#guard twoKinds.wellFormed
#guard !Match.componentsDisjoint collapsedKindsMatch
#guard !collapsedKindsMatch.accepts twoKinds oneLeaf

lemma two_kinds_wellFormed : twoKinds.WellFormed := by decide

lemma collapsed_match_refused : ¬ collapsedKindsMatch.Accepts twoKinds oneLeaf := by decide

/-- **Family-level obstruction.** This is not an artefact of the displayed match.  No
accepted match exists from two metrologically distinct declared sources into the single
vertex left by numeric CSE.  Acceptance requires a nonempty in-range component set for
each declared node and makes the component assignment injective; the one-vertex target
cannot satisfy both requirements. -/
theorem no_accepted_match_after_kind_erasure (m : Match Nat) :
    ¬ m.Accepts twoKinds oneLeaf := by
  intro hm
  have hA := Match.Acc.of_accepts hm
  have h0decl : 0 ∈ Match.nodesOf twoKinds := by decide
  have h1decl : 1 ∈ Match.nodesOf twoKinds := by decide
  have h0ne := hA.comps_nonempty h0decl
  have h1ne := hA.comps_nonempty h1decl
  cases h0 : m.comps 0 with
  | nil => exact h0ne h0
  | cons v vs =>
      cases h1 : m.comps 1 with
      | nil => exact h1ne h1
      | cons w ws =>
          have hv : v ∈ m.comps 0 := by rw [h0]; simp
          have hw : w ∈ m.comps 1 := by rw [h1]; simp
          have hvlt := hA.comps_lt hv
          have hwlt := hA.comps_lt hw
          have hv0 : v = 0 := by
            simpa [oneLeaf, TapeGraph.size] using hvlt
          have hw0 : w = 0 := by
            simpa [oneLeaf, TapeGraph.size] using hwlt
          subst v
          subst w
          have : (0 : Nat) = 1 := hA.comps_inj hv hw
          omega

/-! ## Axiom profile -/

/-- info: 'PropertyKindCalculus.Experiments.CseProvenanceBoundary.no_accepted_match_after_kind_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_accepted_match_after_kind_erasure

end PropertyKindCalculus.Experiments.CseProvenanceBoundary

end Blanket
