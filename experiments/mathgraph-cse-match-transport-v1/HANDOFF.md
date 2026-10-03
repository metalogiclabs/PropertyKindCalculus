# Handoff

This follow-on converts the CSE/provenance separator into a constructive identity contract.
The headline result is `transport_preserves_protected_partition`; the concrete failure result
is `equal_constants_do_not_respect_distinct_sources`. Both are ordinary Lean proofs.

Run:

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
```

The next proof target is intentionally narrower than “prove CSE correct”: define the graph
and multiplicity fields of `TapeQuotientCertificate`, prove them for `cseCompact`, and combine
them with `CseRespectsMatch` to transport `Match.Accepts`.
