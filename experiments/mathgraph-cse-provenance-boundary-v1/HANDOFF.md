# Handoff

## Result

The current executable CSE equivalence is strictly coarser than protected metrological
identity: equal anonymous constants can be merged even when they stand for distinct
attested sources with different kinds.  `Match.accepts` correctly refuses that collapse.

The family-level Lean theorem is:

```lean
theorem no_accepted_match_after_kind_erasure (m : Match Nat) :
    ¬ m.Accepts twoKinds oneLeaf
```

The control case proves that one compacted vertex *is* acceptable after both emissions are
represented by one provenance source.

## Consequence

The proved weak/strong bisimulation results remain intact.  The missing bridge is a theorem
or certificate connecting the actual CSE remap to an accepted match, either by:

1. preventing CSE from merging protected provenance identities; or
2. constructing and qualifying the minimum provenance quotient under which the merge is
   lawful.

The detailed evidence map and proposed theorem ladder are in [`REPORT.md`](./REPORT.md).
