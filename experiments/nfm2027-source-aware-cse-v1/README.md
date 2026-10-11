# PKC provenance/CSE — bounded research controls

This directory holds an independently maintained **research qualification**, using the public PKC implementation without changing its production CSE pass. It isolates one question relevant to proof-to-code assurance: **when does numerical sharing preserve the declared identity of scientific sources?**

The base is [`nasa-jpl/PropertyKindCalculus@48c1a9c`](https://github.com/nasa-jpl/PropertyKindCalculus/commit/48c1a9c440485c9d5d17d38fb135b6978387b89f). All Lean imports are resolved from the branch's committed `lake-manifest.json`. These controls do **not** implement, release, or measure any unpublished audit tool.

## Experiments

| Source | Checked behaviour | Evidence level |
| --- | --- | --- |
| [`ScopedCseProbe.lean`](ScopedCseProbe.lean) | Equal-valued leaf emissions with the *same externally supplied source ID* may share one vertex | Bounded executable positive control |
| Same | Equal-valued leaves with *different externally supplied source IDs* remain separate and the resulting two-source graph passes PKC's actual `Match.accepts` | Bounded executable positive control |
| Same | Unequal-valued leaves remain distinct; missing source metadata is rejected | Bounded executable negative controls |
| Same | Different source IDs produce different scoped keys, with a pinned Lean axiom profile | Lean theorem about key inequality; **not** a general CSE theorem |
| [`AvsRecordedTapeAudit.lean`](AvsRecordedTapeAudit.lean) | The existing AVS residual + four-Jacobian recorder yields 54 raw nodes, 28 compacted nodes, five outputs, 11 anonymous constant leaves, and 21 pairs of equal-valued anonymous leaves merged by CSE | Reproduced numeric census, pinned by `#guard` |

**Interpretation matters.** The AVS census does *not* establish 21 scientific defects. Structural numeric literals can legitimately repeat and be shared, even when the larger typed source contains different quantity kinds. The unannotated tape does not determine which emissions are independently attested sources. The output therefore explicitly records `UNKNOWN_NOT_RECORDED` and `NOT_INFERRED_FROM_VALUE_BITS`.

The scoped prototype is supplied with source classes by its caller. It does **not** harvest them from a science model, infer member-call/occurrence identity, establish general CSE preservation, or verify emitted CPU/GPU code. A real-model provenance certificate additionally requires authoritative source/occurrence annotations and a checked correspondence before and after compaction.

## How to replay

The [companion workflow](../../.github/workflows/mathgraph-nfm-source-cse.yml) builds the exact imported PKC modules, executes both probes, and fails on any `#guard` discrepancy. The workflow explicitly retrieves the **same pinned** FloatLib commit before Lake dependency resolution, avoiding a Git checkout bootstrap failure without changing dependencies.

For an equivalent prepared Lean environment:

```bash
lake build PropertyKindCalculus.Torch.Paradigm.TapeCodegen PropertyKindCalculus.Graph.Bisimulation
lake env lean experiments/nfm2027-source-aware-cse-v1/ScopedCseProbe.lean
lake build PropertyKindCalculus.Examples.TapeCodegenEndToEnd
lake env lean experiments/nfm2027-source-aware-cse-v1/AvsRecordedTapeAudit.lean
```

**Reference results (11 October 2026):** [source-aware probe on the upstream base](https://github.com/metalogiclabs/PropertyKindCalculus/actions/runs/38116672134) and [actual AVS tape census](https://github.com/metalogiclabs/PropertyKindCalculus/actions/runs/38118870865). The complete separate [matcher qualification](https://github.com/metalogiclabs/PropertyKindCalculus/actions/runs/38116770889) exercises the bounded 18-to-14-node recording, certified match, and protected rejection/ambiguity controls.

## Research boundary

The strongest *negative* theorem is separate from this prototype: [`no_accepted_match_after_kind_erasure`](https://github.com/metalogiclabs/PropertyKindCalculus/blob/f0335f1c80119e68c7e3e61a8690bc46022bc499/experiments/mathgraph-cse-provenance-boundary-v1/CseProvenanceBoundary.lean) proves that two distinct declared attested sources cannot both be matched to a one-vertex tape after their identity has been erased. It is a **constructed counterexample**, not an allegation of an observed error in the deployed AVS application.

No results here imply upstream adoption, institutional endorsement, a completed joint audit comparison, or numeric equivalence between distinct runtime backends. All proposed publication interpretations require the paper authors' review and appropriate disclosure permissions.
