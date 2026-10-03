# Independent review of PKC's provenance--tape correspondence and CSE boundary

**Prepared for:** Nicolas Rouquette and Xiaolan Xu

**Prepared by:** Heath Sanchez, MathGraph / Metalogic Labs

**Reviewed repository:** `nasa-jpl/propertykindcalculus`

**Pinned PKC revision:** `6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9`

**Independent qualification date:** 2026-10-03--04

## Executive finding

PKC's central provenance--execution claim is substantially machine-proved at the pinned
revision. If a well-formed metrology provenance hypergraph and computational tape have an
accepted `Match`, PKC proves:

1. a **strong bisimulation** between the provenance transition system and the formally
   contracted tape; and
2. a **weak bisimulation** between the provenance transition system and the actual tape,
   where carrier-level numerical operations internal to one provenance occurrence are silent.

PKC also proves the semantic consequence required by the methodology: under the denotation
bridge, a matched result depends only on provenance-declared influencers and every observable
kind transition is authorized by a declared occurrence.

The independent MathGraph review then examined the boundary not closed by those theorems:
whether PKC's executable common-subexpression elimination (CSE) may be treated as preserving
metrological provenance merely because it preserves numerical computation.

The unconditional statement is **false**. The current CSE key merges equal anonymous constants.
That merge is lawful when they are repeated emissions of one attested source, but it can erase a
scientific distinction when the equal values belong to two distinct declared sources.

MathGraph converted that counterexample into a positive admission contract and executable
checker. For the actual recorded `y = a * b + e` worked model, the complete qualified chain now
runs:

```text
18-node raw recorded tape
  -> actual cseCompact remap
  -> 14-node compacted tape
  -> provenance-sensitive Boolean audit passes
  -> transported Match.accepts
  -> strong bisimulation with the contracted optimized tape
  -> weak bisimulation with the optimized tape
```

The raw tape repeats four named input emissions. The observed CSE remap shares those repeated
emissions; after duplicate vertex identifiers are canonicalized, the transported match is exactly
PKC's independently authored compacted control match.

This is a stronger result than the original review alone: it validates the abstract capstone,
falsifies an unsafe optimization interpretation, supplies the minimum scientific-identity
contract, makes that contract executable, and demonstrates it on PKC's real recorder/CSE path.

## Manager-level conclusion

The following statement is warranted:

> A PKC computation whose recorded tape admits an accepted provenance match is observationally
> faithful to the authored metrological structure up to silent internal numerical work. At the
> provenance layer, a CSE result may be admitted when an independently checkable certificate shows
> that it preserves provenance-node ownership, realization-interior ownership,
> observable/interior roles, and the target acceptance obligations. PKC's recorded complex worked
> model satisfies this certificate for the actual CSE remap.

This does **not** claim that numerical equality establishes scientific identity, that every future
CSE run automatically carries such a certificate, that the compacted graph is literally
isomorphic to the provenance graph, that arbitrary CSE preserves numerical denotation, or that
code below the tape has been verified.

## Claim ledger

| Claim | Status | Evidence boundary |
|---|---|---|
| Accepted provenance and actual tape are weakly bisimilar | **WARRANTED (PKC)** | `Match.isWeakBisimulation_weak`, under graph well-formedness and `Match.Accepts`. |
| Accepted provenance and PKC's formal contraction are strongly bisimilar | **WARRANTED (PKC)** | `Match.isBisimulation_contracted`. Strong bisimulation is not literal graph isomorphism. |
| The formal contraction preserves actual-tape behavior up to silent steps | **WARRANTED (PKC)** | `Match.isSWBisimulation_contraction`. |
| No undeclared raw value affects the matched result | **WARRANTED CONDITIONALLY (PKC)** | `TapeSeal.semantic_seal`, under its tape well-formedness, accepted-match, reachability, and evaluation hypotheses. |
| Numeric/structural CSE always preserves provenance | **REJECTED (MathGraph)** | Two equal anonymous constants from distinct attested sources collapse to one vertex; no accepted match exists afterward. |
| A provenance-sensitive quotient certificate transports acceptance | **WARRANTED (MathGraph)** | `CseMatchTransport.transport_accepts`. |
| A passing executable quotient audit yields that certificate | **WARRANTED (MathGraph)** | `CseQuotientChecker.TapeQuotientAudit.sound`; the checker is also complete for the certificate. |
| The actual worked-model CSE remap is admissible | **WARRANTED, CONCRETE INSTANCE (MathGraph)** | Runtime `#guard`s pin the recorder/CSE output; `recorded_audit_passes` is a kernel theorem over the reified graph and remap. |
| The optimized worked model retains strong and weak bisimulation | **WARRANTED, CONCRETE INSTANCE (MathGraph)** | `recorded_cse_strong_bisimulation` and `recorded_cse_weak_bisimulation`. |
| Every arbitrary recorded model is matched automatically | **OPEN** | PKC accepts a supplied match; generic inference still requires port names, recording-site identity, realization tables, and an owner decision on scope markers versus dependency closure. |
| Every execution of `cseCompact` automatically produces the quotient certificate | **OPEN** | Requires a generic correctness bridge for the mutable array/hash-map loop or a proof-producing wrapper. |
| `cseCompact` preserves numerical denotation for every tape | **OPEN / OUTSIDE THIS QUALIFICATION** | The new checker establishes provenance admissibility of a target tape; functional correctness of the optimizer is a separate theorem. |
| CUDA code generation, scheduler, checkpoint/resume, or generated machine code preserves tape denotation | **OPEN / OUTSIDE THIS REVIEW** | The bisimulation boundary begins at the accepted tape graph. |
| Scientific attestations are physically true | **OUTSIDE THE FORMAL CLAIM** | Attestations are explicit hypotheses; comparison with nature belongs to scientific validation and uncertainty analysis. |

## What an accepted correspondence means

`Match.accepts` is a Boolean decision procedure. It checks that:

- the tape is ordered;
- every declared node has one or more in-range components;
- component keys are unique and refer only to declared nodes;
- components of distinct provenance nodes are disjoint;
- tape leaves are exactly components of declared sources;
- each non-wire realization is closed, interior-private, progressing, frontier-using, and
  composed of operation vertices;
- realization interiors are mutually disjoint and disjoint from observable components;
- every tape operation is covered; and
- provenance occurrences and realizations cover one another.

These clauses are substantive. PKC's existing mutant adds an unlisted constant leaf and is
rejected specifically by `leavesAreSources`.

## What the MathGraph CSE contract adds

`CseRespectsMatch m q` protects the distinctions that numerical CSE cannot infer:

1. components owned by different provenance nodes may not be identified;
2. interiors owned by different occurrence realizations may not be identified; and
3. a silent interior vertex may not be identified with an observable component.

`TapeQuotientCertificate g T' m q` combines that scientific-identity condition with the
target-side obligations needed to reconstruct `Match.Accepts` after transporting the match.
The certificate deliberately does not contain an `Accepts` field; stable declaration and
occurrence clauses are transported separately, and `transport_accepts` rebuilds the acceptance
conjunction.

`CseQuotientChecker.lean` reifies each certificate field as an inspectable Boolean audit and
proves both directions:

```text
audit passes -> TapeQuotientCertificate
TapeQuotientCertificate -> audit passes
```

A successful executable audit therefore becomes proof evidence for target acceptance and the
existing PKC strong/weak bisimulation capstones.

## Worked-model evidence

The qualified recorder instantiates PKC's complex model `y = a * b + e`, where complex
multiplication is realized by four real partial products. The raw recorder emits 18 vertices
because the two output components rebuild shared input expressions. The actual CSE pass returns:

```text
[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 4, 9, 3, 1, 10, 11, 12, 13]
```

and a 14-vertex tape identical to PKC's pre-existing compacted control graph. The raw match is
kernel-accepted. The executable quotient audit passes for the observed remap. From those facts,
Lean derives target acceptance and both bisimulation theorems.

The evidence deliberately uses two authorities:

- `#guard` evaluates the recorder, Torch-backed CSE pass, graph projection, and exact remap; and
- ordinary Lean theorems establish audit soundness, acceptance transport, and bisimulation on the
  reified graphs.

Accordingly, the result qualifies this concrete executable run. It is not presented as a
family-level theorem about all executions of the imperative CSE loop.

## Positive and negative controls

The package retains four independent controls:

1. **Undeclared constant:** PKC's original mutant is rejected by `leavesAreSources`.
2. **Distinct sources, equal values:** executable CSE merges the constants, the identity audit
   rejects the remap, and a family-level theorem proves no accepted match exists on the
   one-vertex result.
3. **One source, repeated emissions:** the same numerical merge passes the identity and complete
   quotient audits and yields acceptance plus both bisimulations.
4. **Role collision:** a remap identifying a realization interior with an observable component is
   rejected independently of raw value equality.

Together these demonstrate that admission is neither vacuous nor equivalent to disabling CSE.
The protected distinction, not the numerical value, determines whether sharing is lawful.

## Value to Nicolas Rouquette

The review resolves the theoretical question at three levels:

- PKC's weak and strong bisimulation theorems already establish the abstract correspondence under
  accepted matching.
- Literal ordered-hypergraph isomorphism remains a stronger statement than the named Lean theorem
  and should retain the blueprint's quotient qualifications.
- Executable optimization now has a precise admission boundary: preserve the protected match
  partition and re-establish the target acceptance obligations.

The remaining universal theorem is sharply isolated: prove that a match-respecting execution of
`cseCompact` constructs the audit evidence automatically. That is a loop-invariant/code-refinement
problem, not an unresolved question about the bisimulation capstone.

## Value to Xiaolan Xu and the science methodology

For a scientific deployment, the evidence can be organized as three separately reviewable claims:

1. **Authored science:** the provenance graph is sealed, kinded, and explicit about sources and
   attestations.
2. **Admitted realization:** the recorded computational graph has an accepted match to that
   provenance structure.
3. **Admitted optimization:** every merge is checked against protected scientific identity and the
   optimized graph retains an accepted transported match.

This provides a concrete answer to a manager asking why an optimized CPU/GPU graph still represents
the scientist's authored algorithm. It is stronger than numerical regression testing because the
evidence states which dependencies and kind transitions are authorized and rejects a numerically
innocent transformation when it erases provenance.

The final deployment assurance case would add independent evidence below the tape: scheduler and
checkpoint refinement, code-generator correctness, and validation of the compiled CPU/GPU program.

Likewise, the quotient audit does not prove that source and target tapes compute equal numerical
values. It proves that the target remains admissible under the authored provenance match. A full
optimizer assurance case needs both this provenance certificate and a functional-correctness or
denotation-preservation argument for the transform.

## Axiom and placeholder audit

The new headline profiles are:

- quotient-audit soundness: `propext`, `Quot.sound`;
- recorded audit witness: `propext`;
- recorded optimized acceptance: `propext`, `Quot.sound`;
- recorded strong bisimulation: `propext`, `Quot.sound`;
- recorded weak bisimulation: `propext`, `Classical.choice`, `Quot.sound`.

No `sorry`, `admit`, or `native_decide` carries a generalized claim in the qualification package.
Fixed executable controls use `#guard`.

## Reproduction

From the repository root:

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
```

The script rebuilds the relevant PKC graph, CSE, code-generation, and test targets; replays the
original provenance-erasure separator; checks the generic transport proof; checks the executable
audit and its controls; checks the actual recorded-model qualification; and rejects forbidden proof
placeholders in the generalized proof files.

## Evidence map

- Upstream bisimulation capstones: `graph/PropertyKindCalculus/Graph/Bisimulation.lean`
- Upstream semantic seal: `torch/PropertyKindCalculus/Torch/Paradigm/TapeSeal.lean`
- Upstream acceptance definition: `PropertyKindCalculus/Paradigm/TapeGraph.lean`
- Upstream positive and mutant witnesses: `tests/PropertyKindCalculus/Tests/Graph/Bisimulation.lean`
- Original MathGraph CSE separator: `../mathgraph-cse-provenance-boundary-v1/`
- Generic match transport: `CseMatchTransport.lean`
- Executable quotient audit: `CseQuotientChecker.lean`
- Actual recorder/CSE qualification: `RecordedCseQualification.lean`
- Technical detail: `REPORT.md`
- Integration summary: `HANDOFF.md`

## Highest-leverage remaining work

The smallest next experiment is not another conceptual review. It is a proof-producing wrapper
around `cseCompact` that emits the remap together with the finite quotient audit, then refuses code
generation when the audit fails. That would operationalize the result for every recorded model
without first requiring a universal proof of the imperative loop.

In parallel, the generic matcher's policy dependency should be resolved explicitly: recorder scope
markers or dependency-closure membership. Once that owner decision is made, the matcher and CSE
admission checker can compose into an automatic provenance-to-optimized-tape certificate pipeline.
