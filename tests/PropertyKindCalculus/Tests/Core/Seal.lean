/-
# Validation probes — the seal of a module, executable

The executable seal (`Provenance.sealed`, `undeclaredLeaves`) on the influence probe graph and
on its mutant — the same graph with an anonymous mint wired into the output — so that the
check is seen to discriminate: the mutant fails well-formedness *and* the seal, at the node
the mint is. Then the harvested instance: `#kind_seal_decide` on the interval composition's
declared boundary, whose well-formedness and agreement the kernel already decides, adds the
seal theorem by kernel reduction of the executable conclusion.
-/

module

public import PropertyKindCalculus.Tests.Core.Influence
meta import PropertyKindCalculus.Tests.Core.Influence
public import PropertyKindCalculus.Tests.Core.KindIncidence
meta import PropertyKindCalculus.Tests.Core.KindIncidence
-- Private scope only: the kernel reduces the seal through bodies sealed in the core library,
-- as the assembly and contract deciders do in `Tests.Core.KindIncidence`.
import all Init.Prelude
import all PropertyKindCalculus.Provenance
import all PropertyKindCalculus.Influence

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Seal

open PropertyKindCalculus Provenance
open PropertyKindCalculus.Tests.Influence (G)

-- The probe graph is sealed: no output rests on an undeclared leaf.
#guard G.sealed
#guard G.outputs == ["out", "mid"]
#guard G.undeclaredLeaves "out" == []
#guard G.undeclaredLeaves "mid" == []

/-- The mutant: the probe graph with an anonymous mint `m` — a `derived` introduction no
occurrence produces — wired into the output in place of the gated ingest. -/
def Gmut : Provenance String String where
  ports := G.ports
  intros := G.intros ++ [⟨"m", "kB", .derived⟩]
  occurrences := [
    ⟨.product, [("in1", "kA"), ("att", "kA")], "mid", "kB", "probe", .anonymous⟩,
    ⟨.product, [("mid", "kB"), ("m", "kB")], "out", "kC", "probe", .anonymous⟩]
  exits := ["mid"]

-- The hypothesis fails and the conclusion fails, at the same node.
#guard !Gmut.wellFormed
#guard !Gmut.sealed
#guard Gmut.undeclaredLeaves "out" == ["m"]
#guard Gmut.undeclaredLeaves "mid" == []

/-! ## The harvested instance — the kernel decides the executable conclusion -/

/--
info: kernel-accepted: every output of the kind assembly rests on declared sources only (theorem 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxLet.kindSealed')
-/
#guard_msgs in #kind_seal_decide KindIncidence.endOfBoxBoundary

/-- info: 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxLet.kindSealed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms KindIncidence.endOfBoxLet.kindSealed

end PropertyKindCalculus.Tests.Seal

end Blanket
