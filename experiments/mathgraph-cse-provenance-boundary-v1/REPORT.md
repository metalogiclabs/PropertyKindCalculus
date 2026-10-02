# PKC CSE–provenance boundary qualification

Status: **bounded separator established**

PKC pin: `nasa-jpl/PropertyKindCalculus@6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9`

Prepared independently by: **Heath Sanchez / Metalogic Labs (MathGraph.org)**

Date: 2026-10-02

## Executive result

PKC already proves the central conditional result: whenever a well-formed provenance
hypergraph and a tape graph have an accepted `Match`, the provenance graph is weakly
bisimilar to the tape graph, and strongly bisimilar to the match-defined contracted graph.

The missing theorem is earlier in the pipeline:

> Does the **actual executable CSE pass** preserve enough metrological identity that an
> accepted match still exists, or induce a warranted quotient of provenance against which
> one exists?

For the current `cseCompact`, the unconditional answer is **no**.  The pass keys an
anonymous constant by its operation name, canonical parents, and stored Float bits.  Two
equal constants therefore become one tape vertex even when they represent two distinct
attested sources with different kinds.  But `Match.accepts` requires every declared
provenance node to have an in-range component and requires component ownership to be
injective.  A one-vertex tape cannot be accepted as the realization of those two sources.

The included Lean probe establishes both halves:

1. executable controls show two anonymous `1.0` constants compact from two tape nodes to
   one and project to the one-leaf `TapeGraph`; and
2. `no_accepted_match_after_kind_erasure` proves, for **every** candidate `Match`, that no
   accepted match exists between that one-leaf tape graph and a well-formed provenance
   graph containing two distinct attested sources of different kinds.

The same probe includes the control that matters: after the two emissions are represented
as one metrological source, the one-vertex graph is accepted.  The obstruction is therefore
not sharing itself.  It is sharing before the metrological distinction has been proved
irrelevant.

## What this does—and does not—say

This result does **not** refute PKC's proved bisimulation theorems.  Those theorems are
correctly conditional on an accepted match.  It identifies the missing acquisition bridge
between the actual CSE output and that premise.

It also separates three notions that are easy to conflate:

| Object | What it does | Current status |
|---|---|---|
| `TapeCSE.cseCompact` | Hash-conses identical recorded computations | Executable; structural and denotational preservation proved under the documented hypotheses |
| `Match.contracted` | Removes the silent interior of each accepted realization at the LTS level | Defined from `g` and `m`; strong bisimulation with provenance proved |
| Provenance quotient by derivation equality | Merges provenance identities so actual computation sharing is semantically lawful | Described in the blueprint; no definition or generic bridge theorem found at this pin |

In particular, `cseCompact` is not itself the contraction used by
`isBisimulation_contracted`.  The recorded complex example remains a 14-vertex tape after
CSE for a five-node provenance graph; the strong theorem concerns the separately defined
contracted LTS.  Reaching literal ordered-hypergraph isomorphism therefore requires an
additional quotient/contraction construction, not CSE alone.

## Exact residual

Let `q` be the old-to-new node map returned by CSE and `m.comps a` the tape components of a
provenance node `a`.  A necessary condition for transporting an accepted match through CSE
without changing provenance is:

```text
u ∈ m.comps a ∧ v ∈ m.comps b ∧ q(u) = q(v)  →  a = b
```

That is only the observable part.  A complete transport theorem must also control sharing
of realization interiors: CSE can merge identical interior operations belonging to
different occurrences, while current acceptance requires interiors to be disjoint and
private.

There are therefore two sound completion routes.

### Route A — strict, provenance-aware compaction

Refine the CSE identity at protected boundaries with a semantic token carrying source
identity, kind/role, and realization ownership where required.  Then prove that the remap
is injective on observable components and respects realization boundaries.  This preserves
the authored provenance graph exactly.

### Route B — certified consequential quotient

Keep aggressive computational CSE, but derive a provenance equivalence relation from the
merges and admit it only when it is a congruence for every protected observation: kind,
source/attestation identity, boundary role, occurrence family and operand position,
uncertainty lineage, and declared outputs.  Construct the quotient provenance graph and
prove that the CSE tape has an accepted match against it.  Equal raw values alone can never
discharge this obligation.

Route B matches the blueprint's phrase “hypergraph quotiented by derivation equality,” but
turns that phrase into a checkable object with an explicit qualification boundary.

## Recommended theorem ladder

1. Define `CseRespectsMatch g T m q`, initially as observable injectivity plus
   realization-ownership compatibility.
2. Prove `transportMatch`: from `m.Accepts g T` and `CseRespectsMatch …`, construct an
   accepted match on `ofTape (cseCompact t).1`.
3. Define a candidate provenance quotient and a Boolean/Prop correspondence for its
   admissibility.
4. Prove the quotient is well formed and preserves the selected protected observations.
5. Prove an accepted match between the quotient provenance and the actual compacted tape.
6. Reuse the existing `isWeakBisimulation_weak` and `isBisimulation_contracted` theorems.
7. Define the final component quotient of `Match.contracted`; prove ordered-hypergraph
   isomorphism to the admitted provenance quotient, or retain a precisely typed residual if
   component multiplicity prevents isomorphism.

This ladder gives Nicolas the missing computer-science theorem without weakening the
existing match semantics, and gives the science assurance case a concrete answer to the
question: **which computational optimizations were allowed to erase which scientific
distinctions, and under what proof?**

## Why this matters for the soil-moisture demonstration

The manager-facing claim should be an end-to-end assurance chain, not merely “the model is
written in Lean”:

```text
kinded/attested inputs
  → sealed PKC provenance
  → recorded tape with an accepted match
  → certified provenance-safe CSE or certified provenance quotient
  → CPU/GPU lowering and execution
  → result + provenance/qualification receipt
```

For Xiaolan's science case, the highest-value next instance is one representative
soil-moisture path already present in the project—preferably the Water Cloud Model forward
and closed-form retrieval—carried through this chain with its domain condition,
uncertainty budget, selected output, and exact CSE quotient certificate.  That would make
the theoretical contribution visible as a NASA-relevant evidence package rather than an
isolated graph theorem.

## Evidence and reproduction

The probe is [`CseProvenanceBoundary.lean`](./CseProvenanceBoundary.lean).

Run from the repository root after resolving the pinned Lake dependencies:

```bash
lake build PropertyKindCalculus.Torch.Paradigm.TapeCodegen \
  PropertyKindCalculus.Torch.Paradigm.TapeCse \
  PropertyKindCalculus.Graph.Bisimulation
lake env lean experiments/mathgraph-cse-provenance-boundary-v1/CseProvenanceBoundary.lean
lake build PropertyKindCalculus.Tests.Graph.Bisimulation \
  PropertyKindCalculus.Tests.Torch.TapeSeal
```

At the pinned commit the probe contains no `sorry`, `admit`, or `native_decide`.  The
family-level obstruction has the standard PKC axiom profile
`[propext, Classical.choice, Quot.sound]`; the two CSE outcomes are fixed executable
controls and are not presented as family-level theorems.

## Scope boundary

Established here:

- the present CSE key merges equal anonymous constants;
- the resulting graph can represent repeated emission of one source;
- it cannot admit two distinct kinded sources under any current `Match`;
- the precise failure is the incompatibility between computational equivalence and
  protected metrological identity.

Not yet established:

- a generic source-to-tape matcher;
- a complete characterization of every merge performed by CSE;
- the minimum admissible provenance congruence for the full PKC observation language;
- the generic transport theorem or ordered-hypergraph isomorphism;
- the CPU/GPU/code-generation correctness boundary below the tape;
- scientific accuracy against nature or truth of attestations.
