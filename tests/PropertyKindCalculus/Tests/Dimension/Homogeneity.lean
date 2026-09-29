/-
# Validation probes — dimensional homogeneity along the hypergraph (capstone 3)

Inhabitation, negative and axiom-profile probes for `DimensionalHomogeneity`: a one-edge
hypergraph `x · y → z` over kinds dimensioned `L`, `L` and `L²`, whose coverage verdict the
kernel decides through the executable `coherent`; the capstone applied to it; and the mutant
`L · L → L` — the refuted edge the coverage command pins — where the hypothesis fails and
the conclusion fails together: the assignment that follows the rules from the same sources
gives `z` the dimension `L²`, not the declared `L`. `homogeneity_witnesses` conjoins the
instance and the mutant for the blueprint's witness node.

Kinds are strings and nodes are numbers; the dimensions are PhysLib's, so the equalities are
decided by the kernel's reduction of the rational exponent arithmetic (`decide +kernel`), as
the coverage command decides them.
-/

module

public import PropertyKindCalculus.DimensionalHomogeneity
meta import PropertyKindCalculus.DimensionalHomogeneity

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Homogeneity

open PropertyKindCalculus Provenance
open PropertyKindCalculus.DimensionalHomogeneity (dimRule dimensional_homogeneity)

/-- The declared dimension of each kind: `L` is a length, `L2` an area. -/
def dimOf : String → Option (Dimension LTMCTDimensionBase)
  | "L" => some Dim.length
  | "L2" => some (Dim.length * Dim.length)
  | _ => none

/-- The coherent instance: `x · y → z` with `z` an area. -/
def gL : Provenance Nat String where
  ports := [⟨0, "L", .input⟩, ⟨1, "L", .input⟩, ⟨2, "L2", .output⟩]
  intros := []
  occurrences := [⟨.product, [(0, "L"), (1, "L")], 2, "L2", "probe", .anonymous⟩]
  exits := []

/-- The mutant: the same edge with `z` declared a length — `L · L → L`, the edge the
coverage command refutes. -/
def gLmut : Provenance Nat String where
  ports := [⟨0, "L", .input⟩, ⟨1, "L", .input⟩, ⟨2, "L", .output⟩]
  intros := []
  occurrences := [⟨.product, [(0, "L"), (1, "L")], 2, "L", "probe", .anonymous⟩]
  exits := []

/-- The assignment that follows the rules from the sources: `z` is an area, whatever its
declaration says. -/
def computed : Nat → Option (Dimension LTMCTDimensionBase)
  | 0 => some Dim.length
  | 1 => some Dim.length
  | 2 => some (Dim.length * Dim.length)
  | _ => none

/-! ## Inhabitation: the coverage verdict decided, the capstone applied -/

lemma gL_wellFormed : gL.WellFormed := by decide

lemma gL_coherent : ∀ o ∈ gL.occurrences, coherent dimRule (declaredDim dimOf gL) o = true := by
  decide +kernel

lemma gL_homomorphic : ∀ o ∈ gL.occurrences, Homomorphic dimRule (declaredDim dimOf gL) o :=
  fun o ho => coherent_iff.mp (gL_coherent o ho)

/-- The capstone, applied: every assignment following the rules from the declared source
dimensions agrees with the declared assignment on every known node — here, at `z`. -/
example : ∀ x ∈ gL.known, computed x = declaredDim dimOf gL x :=
  (dimensional_homogeneity gL_wellFormed dimOf gL_homomorphic
    (fun o ho => coherent_iff.mp (by revert o ho; decide +kernel))
    (fun s hs => by revert s hs; decide +kernel)).1

/-! ## The mutant: the hypothesis fails and the conclusion fails, together -/

lemma gLmut_wellFormed : gLmut.WellFormed := by decide

/-- The refuted edge: the declared assignment is not homomorphic along it. -/
lemma gLmut_incoherent :
    ∃ o ∈ gLmut.occurrences, coherent dimRule (declaredDim dimOf gLmut) o = false := by
  decide +kernel

/-- The rule-following assignment is homomorphic along the same edge… -/
lemma computed_coherent_mut :
    ∀ o ∈ gLmut.occurrences, coherent dimRule computed o = true := by
  decide +kernel

/-- …agrees with the declaration on the sources… -/
lemma computed_agrees_sources_mut : ∀ s ∈ gLmut.sources, computed s = declaredDim dimOf gLmut s := by
  decide +kernel

/-- …and disagrees with it at the output: the conclusion fails where the hypothesis does. -/
lemma computed_ne_declared_mut : computed 2 ≠ declaredDim dimOf gLmut 2 := by
  decide +kernel

/-- **Non-vacuity of dimensional homogeneity**: the instance's verdict is coherent and the
capstone applies; the mutant's verdict is refuted and the rule-following assignment departs
from the declared one at the output. -/
lemma homogeneity_witnesses :
    (∀ o ∈ gL.occurrences, coherent dimRule (declaredDim dimOf gL) o = true) ∧
      (∃ o ∈ gLmut.occurrences, coherent dimRule (declaredDim dimOf gLmut) o = false) ∧
      computed 2 ≠ declaredDim dimOf gLmut 2 :=
  ⟨gL_coherent, gLmut_incoherent, computed_ne_declared_mut⟩

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.DimensionalHomogeneity.dimensional_homogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PropertyKindCalculus.DimensionalHomogeneity.dimensional_homogeneity

/-- info: 'PropertyKindCalculus.Provenance.homogeneity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Provenance.homogeneity

end PropertyKindCalculus.Tests.Homogeneity

end Blanket
