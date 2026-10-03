# Handoff

This package now qualifies the PKC provenance--tape claim through the executable CSE boundary.

The headline chain is:

```text
actual 18-vertex recording
  -> actual cseCompact remap
  -> 14-vertex PKC control tape
  -> executable provenance-sensitive audit
  -> transported Match.accepts
  -> PKC strong and weak bisimulation theorems
```

The generic theorem `transport_accepts` proves that source acceptance plus a
`TapeQuotientCertificate` yields target acceptance. `TapeQuotientAudit.sound` and
`TapeQuotientAudit.complete` make that certificate an executable admission decision.
`recorded_cse_accepts`, `recorded_cse_strong_bisimulation`, and
`recorded_cse_weak_bisimulation` instantiate the chain on PKC's actual recorded complex model.

The controls retain both sides of the scientific boundary: equal values from distinct declared
sources are rejected, while repeated emissions of one source are admitted. A separate role
collision and PKC's undeclared-leaf mutant prevent vacuous acceptance.

Run:

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
```

Read [`INDEPENDENT_REVIEW.md`](./INDEPENDENT_REVIEW.md) for the manager-facing assessment and
[`REPORT.md`](./REPORT.md) for the technical boundary.

The highest-leverage next step is a proof-producing wrapper around `cseCompact` that emits the
finite audit and refuses code generation when it fails. A universal loop theorem and a generic
recorded-tape matcher remain separate work. Strong bisimulation is established; literal graph
isomorphism, generic numerical denotation preservation by CSE, and correctness below the tape
(CUDA, scheduling, checkpoint/resume, machine code) are not claimed.
